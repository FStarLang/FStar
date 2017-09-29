
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
| uu____9 -> begin
false
end))


let uu___is_Medium : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Medium -> begin
true
end
| uu____14 -> begin
false
end))


let uu___is_High : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| High -> begin
true
end
| uu____19 -> begin
false
end))


let uu___is_Extreme : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Extreme -> begin
true
end
| uu____24 -> begin
false
end))


let uu___is_Other : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Other (_0) -> begin
true
end
| uu____30 -> begin
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
| uu____66 -> begin
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
| uu____80 -> begin
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
| uu____94 -> begin
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
| uu____108 -> begin
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
| uu____124 -> begin
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
| uu____143 -> begin
false
end))


let mk_bool : Prims.bool  ->  option_val = (fun _0_28 -> Bool (_0_28))


let mk_string : Prims.string  ->  option_val = (fun _0_29 -> String (_0_29))


let mk_path : Prims.string  ->  option_val = (fun _0_30 -> Path (_0_30))


let mk_int : Prims.int  ->  option_val = (fun _0_31 -> Int (_0_31))


let mk_list : option_val Prims.list  ->  option_val = (fun _0_32 -> List (_0_32))

type options =
| Set
| Reset
| Restore


let uu___is_Set : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Set -> begin
true
end
| uu____165 -> begin
false
end))


let uu___is_Reset : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reset -> begin
true
end
| uu____170 -> begin
false
end))


let uu___is_Restore : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Restore -> begin
true
end
| uu____175 -> begin
false
end))


let __unit_tests__ : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let __unit_tests : Prims.unit  ->  Prims.bool = (fun uu____188 -> (FStar_ST.op_Bang __unit_tests__))


let __set_unit_tests : Prims.unit  ->  Prims.unit = (fun uu____238 -> (FStar_ST.op_Colon_Equals __unit_tests__ true))


let __clear_unit_tests : Prims.unit  ->  Prims.unit = (fun uu____288 -> (FStar_ST.op_Colon_Equals __unit_tests__ false))


let as_bool : option_val  ->  Prims.bool = (fun uu___48_338 -> (match (uu___48_338) with
| Bool (b) -> begin
b
end
| uu____340 -> begin
(failwith "Impos: expected Bool")
end))


let as_int : option_val  ->  Prims.int = (fun uu___49_344 -> (match (uu___49_344) with
| Int (b) -> begin
b
end
| uu____346 -> begin
(failwith "Impos: expected Int")
end))


let as_string : option_val  ->  Prims.string = (fun uu___50_350 -> (match (uu___50_350) with
| String (b) -> begin
b
end
| Path (b) -> begin
(FStar_Common.try_convert_file_name_to_mixed b)
end
| uu____353 -> begin
(failwith "Impos: expected String")
end))


let as_list' : option_val  ->  option_val Prims.list = (fun uu___51_359 -> (match (uu___51_359) with
| List (ts) -> begin
ts
end
| uu____365 -> begin
(failwith "Impos: expected List")
end))


let as_list : 'Auu____374 . (option_val  ->  'Auu____374)  ->  option_val  ->  'Auu____374 Prims.list = (fun as_t x -> (

let uu____390 = (as_list' x)
in (FStar_All.pipe_right uu____390 (FStar_List.map as_t))))


let as_option : 'Auu____403 . (option_val  ->  'Auu____403)  ->  option_val  ->  'Auu____403 FStar_Pervasives_Native.option = (fun as_t uu___52_416 -> (match (uu___52_416) with
| Unset -> begin
FStar_Pervasives_Native.None
end
| v1 -> begin
(

let uu____420 = (as_t v1)
in FStar_Pervasives_Native.Some (uu____420))
end))


type optionstate =
option_val FStar_Util.smap


let fstar_options : optionstate Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let peek : Prims.unit  ->  optionstate = (fun uu____439 -> (

let uu____440 = (FStar_ST.op_Bang fstar_options)
in (FStar_List.hd uu____440)))


let pop : Prims.unit  ->  Prims.unit = (fun uu____496 -> (

let uu____497 = (FStar_ST.op_Bang fstar_options)
in (match (uu____497) with
| [] -> begin
(failwith "TOO MANY POPS!")
end
| (uu____550)::[] -> begin
(failwith "TOO MANY POPS!")
end
| (uu____551)::tl1 -> begin
(FStar_ST.op_Colon_Equals fstar_options tl1)
end)))


let push : Prims.unit  ->  Prims.unit = (fun uu____608 -> (

let uu____609 = (

let uu____612 = (

let uu____615 = (peek ())
in (FStar_Util.smap_copy uu____615))
in (

let uu____618 = (FStar_ST.op_Bang fstar_options)
in (uu____612)::uu____618))
in (FStar_ST.op_Colon_Equals fstar_options uu____609)))


let set : optionstate  ->  Prims.unit = (fun o -> (

let uu____729 = (FStar_ST.op_Bang fstar_options)
in (match (uu____729) with
| [] -> begin
(failwith "set on empty option stack")
end
| (uu____782)::os -> begin
(FStar_ST.op_Colon_Equals fstar_options ((o)::os))
end)))


let set_option : Prims.string  ->  option_val  ->  Prims.unit = (fun k v1 -> (

let uu____844 = (peek ())
in (FStar_Util.smap_add uu____844 k v1)))


let set_option' : (Prims.string * option_val)  ->  Prims.unit = (fun uu____854 -> (match (uu____854) with
| (k, v1) -> begin
(set_option k v1)
end))


let with_saved_options : 'a . (Prims.unit  ->  'a)  ->  'a = (fun f -> ((push ());
(

let retv = (f ())
in ((pop ());
retv;
));
))


let light_off_files : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let add_light_off_file : Prims.string  ->  Prims.unit = (fun filename -> (

let uu____895 = (

let uu____898 = (FStar_ST.op_Bang light_off_files)
in (filename)::uu____898)
in (FStar_ST.op_Colon_Equals light_off_files uu____895)))


let defaults : (Prims.string * option_val) Prims.list = ((("__temp_no_proj"), (List ([]))))::((("_fstar_home"), (String (""))))::((("_include_path"), (List ([]))))::((("admit_smt_queries"), (Bool (false))))::((("admit_except"), (Unset)))::((("cache_checked_modules"), (Bool (false))))::((("codegen"), (Unset)))::((("codegen-lib"), (List ([]))))::((("debug"), (List ([]))))::((("debug_level"), (List ([]))))::((("dep"), (Unset)))::((("detail_errors"), (Bool (false))))::((("detail_hint_replay"), (Bool (false))))::((("doc"), (Bool (false))))::((("dump_module"), (List ([]))))::((("eager_inference"), (Bool (false))))::((("explicit_deps"), (Bool (false))))::((("extract_all"), (Bool (false))))::((("extract_module"), (List ([]))))::((("extract_namespace"), (List ([]))))::((("fs_typ_app"), (Bool (false))))::((("fstar_home"), (Unset)))::((("full_context_dependency"), (Bool (true))))::((("gen_native_tactics"), (Unset)))::((("hide_genident_nums"), (Bool (false))))::((("hide_uvar_nums"), (Bool (false))))::((("hint_info"), (Bool (false))))::((("hint_file"), (Unset)))::((("in"), (Bool (false))))::((("ide"), (Bool (false))))::((("include"), (List ([]))))::((("indent"), (Bool (false))))::((("initial_fuel"), (Int ((Prims.parse_int "2")))))::((("initial_ifuel"), (Int ((Prims.parse_int "1")))))::((("lax"), (Bool (false))))::((("load"), (List ([]))))::((("log_queries"), (Bool (false))))::((("log_types"), (Bool (false))))::((("max_fuel"), (Int ((Prims.parse_int "8")))))::((("max_ifuel"), (Int ((Prims.parse_int "2")))))::((("min_fuel"), (Int ((Prims.parse_int "1")))))::((("MLish"), (Bool (false))))::((("n_cores"), (Int ((Prims.parse_int "1")))))::((("no_default_includes"), (Bool (false))))::((("no_extract"), (List ([]))))::((("no_location_info"), (Bool (false))))::((("no_tactics"), (Bool (false))))::((("odir"), (Unset)))::((("prims"), (Unset)))::((("pretype"), (Bool (true))))::((("prims_ref"), (Unset)))::((("print_bound_var_types"), (Bool (false))))::((("print_effect_args"), (Bool (false))))::((("print_full_names"), (Bool (false))))::((("print_implicits"), (Bool (false))))::((("print_universes"), (Bool (false))))::((("print_z3_statistics"), (Bool (false))))::((("prn"), (Bool (false))))::((("query_stats"), (Bool (false))))::((("record_hints"), (Bool (false))))::((("reuse_hint_for"), (Unset)))::((("show_signatures"), (List ([]))))::((("silent"), (Bool (false))))::((("smt"), (Unset)))::((("smtencoding.elim_box"), (Bool (false))))::((("smtencoding.nl_arith_repr"), (String ("boxwrap"))))::((("smtencoding.l_arith_repr"), (String ("boxwrap"))))::((("split_cases"), (Int ((Prims.parse_int "0")))))::((("tactic_trace"), (Bool (false))))::((("tactic_trace_d"), (Int ((Prims.parse_int "0")))))::((("timing"), (Bool (false))))::((("trace_error"), (Bool (false))))::((("ugly"), (Bool (false))))::((("unthrottle_inductives"), (Bool (false))))::((("unsafe_tactic_exec"), (Bool (false))))::((("use_native_tactics"), (Unset)))::((("use_eq_at_higher_order"), (Bool (false))))::((("use_hints"), (Bool (false))))::((("using_facts_from"), (Unset)))::((("verify"), (Bool (true))))::((("verify_all"), (Bool (false))))::((("verify_module"), (List ([]))))::((("warn_default_effects"), (Bool (false))))::((("z3refresh"), (Bool (false))))::((("z3rlimit"), (Int ((Prims.parse_int "5")))))::((("z3rlimit_factor"), (Int ((Prims.parse_int "1")))))::((("z3seed"), (Int ((Prims.parse_int "0")))))::((("z3cliopt"), (List ([]))))::((("__no_positivity"), (Bool (false))))::((("__ml_no_eta_expand_coertions"), (Bool (false))))::[]


let init : Prims.unit  ->  Prims.unit = (fun uu____1374 -> (

let o = (peek ())
in ((FStar_Util.smap_clear o);
(FStar_All.pipe_right defaults (FStar_List.iter set_option'));
)))


let clear : Prims.unit  ->  Prims.unit = (fun uu____1390 -> (

let o = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_ST.op_Colon_Equals fstar_options ((o)::[]));
(FStar_ST.op_Colon_Equals light_off_files []);
(init ());
)))


let _run : Prims.unit = (clear ())


let get_option : Prims.string  ->  option_val = (fun s -> (

let uu____1504 = (

let uu____1507 = (peek ())
in (FStar_Util.smap_try_find uu____1507 s))
in (match (uu____1504) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Impossible: option " (Prims.strcat s " not found")))
end
| FStar_Pervasives_Native.Some (s1) -> begin
s1
end)))


let lookup_opt : 'Auu____1517 . Prims.string  ->  (option_val  ->  'Auu____1517)  ->  'Auu____1517 = (fun s c -> (c (get_option s)))


let get_admit_smt_queries : Prims.unit  ->  Prims.bool = (fun uu____1534 -> (lookup_opt "admit_smt_queries" as_bool))


let get_admit_except : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1540 -> (lookup_opt "admit_except" (as_option as_string)))


let get_cache_checked_modules : Prims.unit  ->  Prims.bool = (fun uu____1546 -> (lookup_opt "cache_checked_modules" as_bool))


let get_codegen : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1552 -> (lookup_opt "codegen" (as_option as_string)))


let get_codegen_lib : Prims.unit  ->  Prims.string Prims.list = (fun uu____1560 -> (lookup_opt "codegen-lib" (as_list as_string)))


let get_debug : Prims.unit  ->  Prims.string Prims.list = (fun uu____1568 -> (lookup_opt "debug" (as_list as_string)))


let get_debug_level : Prims.unit  ->  Prims.string Prims.list = (fun uu____1576 -> (lookup_opt "debug_level" (as_list as_string)))


let get_dep : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1584 -> (lookup_opt "dep" (as_option as_string)))


let get_detail_errors : Prims.unit  ->  Prims.bool = (fun uu____1590 -> (lookup_opt "detail_errors" as_bool))


let get_detail_hint_replay : Prims.unit  ->  Prims.bool = (fun uu____1594 -> (lookup_opt "detail_hint_replay" as_bool))


let get_doc : Prims.unit  ->  Prims.bool = (fun uu____1598 -> (lookup_opt "doc" as_bool))


let get_dump_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____1604 -> (lookup_opt "dump_module" (as_list as_string)))


let get_eager_inference : Prims.unit  ->  Prims.bool = (fun uu____1610 -> (lookup_opt "eager_inference" as_bool))


let get_explicit_deps : Prims.unit  ->  Prims.bool = (fun uu____1614 -> (lookup_opt "explicit_deps" as_bool))


let get_extract_all : Prims.unit  ->  Prims.bool = (fun uu____1618 -> (lookup_opt "extract_all" as_bool))


let get_extract_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____1624 -> (lookup_opt "extract_module" (as_list as_string)))


let get_extract_namespace : Prims.unit  ->  Prims.string Prims.list = (fun uu____1632 -> (lookup_opt "extract_namespace" (as_list as_string)))


let get_fs_typ_app : Prims.unit  ->  Prims.bool = (fun uu____1638 -> (lookup_opt "fs_typ_app" as_bool))


let get_fstar_home : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1644 -> (lookup_opt "fstar_home" (as_option as_string)))


let get_gen_native_tactics : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1652 -> (lookup_opt "gen_native_tactics" (as_option as_string)))


let get_hide_genident_nums : Prims.unit  ->  Prims.bool = (fun uu____1658 -> (lookup_opt "hide_genident_nums" as_bool))


let get_hide_uvar_nums : Prims.unit  ->  Prims.bool = (fun uu____1662 -> (lookup_opt "hide_uvar_nums" as_bool))


let get_hint_info : Prims.unit  ->  Prims.bool = (fun uu____1666 -> (lookup_opt "hint_info" as_bool))


let get_hint_file : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1672 -> (lookup_opt "hint_file" (as_option as_string)))


let get_in : Prims.unit  ->  Prims.bool = (fun uu____1678 -> (lookup_opt "in" as_bool))


let get_ide : Prims.unit  ->  Prims.bool = (fun uu____1682 -> (lookup_opt "ide" as_bool))


let get_include : Prims.unit  ->  Prims.string Prims.list = (fun uu____1688 -> (lookup_opt "include" (as_list as_string)))


let get_indent : Prims.unit  ->  Prims.bool = (fun uu____1694 -> (lookup_opt "indent" as_bool))


let get_initial_fuel : Prims.unit  ->  Prims.int = (fun uu____1698 -> (lookup_opt "initial_fuel" as_int))


let get_initial_ifuel : Prims.unit  ->  Prims.int = (fun uu____1702 -> (lookup_opt "initial_ifuel" as_int))


let get_lax : Prims.unit  ->  Prims.bool = (fun uu____1706 -> (lookup_opt "lax" as_bool))


let get_load : Prims.unit  ->  Prims.string Prims.list = (fun uu____1712 -> (lookup_opt "load" (as_list as_string)))


let get_log_queries : Prims.unit  ->  Prims.bool = (fun uu____1718 -> (lookup_opt "log_queries" as_bool))


let get_log_types : Prims.unit  ->  Prims.bool = (fun uu____1722 -> (lookup_opt "log_types" as_bool))


let get_max_fuel : Prims.unit  ->  Prims.int = (fun uu____1726 -> (lookup_opt "max_fuel" as_int))


let get_max_ifuel : Prims.unit  ->  Prims.int = (fun uu____1730 -> (lookup_opt "max_ifuel" as_int))


let get_min_fuel : Prims.unit  ->  Prims.int = (fun uu____1734 -> (lookup_opt "min_fuel" as_int))


let get_MLish : Prims.unit  ->  Prims.bool = (fun uu____1738 -> (lookup_opt "MLish" as_bool))


let get_n_cores : Prims.unit  ->  Prims.int = (fun uu____1742 -> (lookup_opt "n_cores" as_int))


let get_no_default_includes : Prims.unit  ->  Prims.bool = (fun uu____1746 -> (lookup_opt "no_default_includes" as_bool))


let get_no_extract : Prims.unit  ->  Prims.string Prims.list = (fun uu____1752 -> (lookup_opt "no_extract" (as_list as_string)))


let get_no_location_info : Prims.unit  ->  Prims.bool = (fun uu____1758 -> (lookup_opt "no_location_info" as_bool))


let get_odir : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1764 -> (lookup_opt "odir" (as_option as_string)))


let get_ugly : Prims.unit  ->  Prims.bool = (fun uu____1770 -> (lookup_opt "ugly" as_bool))


let get_prims : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1776 -> (lookup_opt "prims" (as_option as_string)))


let get_print_bound_var_types : Prims.unit  ->  Prims.bool = (fun uu____1782 -> (lookup_opt "print_bound_var_types" as_bool))


let get_print_effect_args : Prims.unit  ->  Prims.bool = (fun uu____1786 -> (lookup_opt "print_effect_args" as_bool))


let get_print_full_names : Prims.unit  ->  Prims.bool = (fun uu____1790 -> (lookup_opt "print_full_names" as_bool))


let get_print_implicits : Prims.unit  ->  Prims.bool = (fun uu____1794 -> (lookup_opt "print_implicits" as_bool))


let get_print_universes : Prims.unit  ->  Prims.bool = (fun uu____1798 -> (lookup_opt "print_universes" as_bool))


let get_print_z3_statistics : Prims.unit  ->  Prims.bool = (fun uu____1802 -> (lookup_opt "print_z3_statistics" as_bool))


let get_prn : Prims.unit  ->  Prims.bool = (fun uu____1806 -> (lookup_opt "prn" as_bool))


let get_query_stats : Prims.unit  ->  Prims.bool = (fun uu____1810 -> (lookup_opt "query_stats" as_bool))


let get_record_hints : Prims.unit  ->  Prims.bool = (fun uu____1814 -> (lookup_opt "record_hints" as_bool))


let get_reuse_hint_for : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1820 -> (lookup_opt "reuse_hint_for" (as_option as_string)))


let get_show_signatures : Prims.unit  ->  Prims.string Prims.list = (fun uu____1828 -> (lookup_opt "show_signatures" (as_list as_string)))


let get_silent : Prims.unit  ->  Prims.bool = (fun uu____1834 -> (lookup_opt "silent" as_bool))


let get_smt : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1840 -> (lookup_opt "smt" (as_option as_string)))


let get_smtencoding_elim_box : Prims.unit  ->  Prims.bool = (fun uu____1846 -> (lookup_opt "smtencoding.elim_box" as_bool))


let get_smtencoding_nl_arith_repr : Prims.unit  ->  Prims.string = (fun uu____1850 -> (lookup_opt "smtencoding.nl_arith_repr" as_string))


let get_smtencoding_l_arith_repr : Prims.unit  ->  Prims.string = (fun uu____1854 -> (lookup_opt "smtencoding.l_arith_repr" as_string))


let get_split_cases : Prims.unit  ->  Prims.int = (fun uu____1858 -> (lookup_opt "split_cases" as_int))


let get_tactic_trace : Prims.unit  ->  Prims.bool = (fun uu____1862 -> (lookup_opt "tactic_trace" as_bool))


let get_tactic_trace_d : Prims.unit  ->  Prims.int = (fun uu____1866 -> (lookup_opt "tactic_trace_d" as_int))


let get_timing : Prims.unit  ->  Prims.bool = (fun uu____1870 -> (lookup_opt "timing" as_bool))


let get_trace_error : Prims.unit  ->  Prims.bool = (fun uu____1874 -> (lookup_opt "trace_error" as_bool))


let get_unthrottle_inductives : Prims.unit  ->  Prims.bool = (fun uu____1878 -> (lookup_opt "unthrottle_inductives" as_bool))


let get_unsafe_tactic_exec : Prims.unit  ->  Prims.bool = (fun uu____1882 -> (lookup_opt "unsafe_tactic_exec" as_bool))


let get_use_eq_at_higher_order : Prims.unit  ->  Prims.bool = (fun uu____1886 -> (lookup_opt "use_eq_at_higher_order" as_bool))


let get_use_hints : Prims.unit  ->  Prims.bool = (fun uu____1890 -> (lookup_opt "use_hints" as_bool))


let get_use_native_tactics : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1896 -> (lookup_opt "use_native_tactics" (as_option as_string)))


let get_use_tactics : Prims.unit  ->  Prims.bool = (fun uu____1902 -> (

let uu____1903 = (lookup_opt "no_tactics" as_bool)
in (not (uu____1903))))


let get_using_facts_from : Prims.unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____1911 -> (lookup_opt "using_facts_from" (as_option (as_list as_string))))


let get_verify_all : Prims.unit  ->  Prims.bool = (fun uu____1921 -> (lookup_opt "verify_all" as_bool))


let get_verify_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____1927 -> (lookup_opt "verify_module" (as_list as_string)))


let get___temp_no_proj : Prims.unit  ->  Prims.string Prims.list = (fun uu____1935 -> (lookup_opt "__temp_no_proj" (as_list as_string)))


let get_version : Prims.unit  ->  Prims.bool = (fun uu____1941 -> (lookup_opt "version" as_bool))


let get_warn_default_effects : Prims.unit  ->  Prims.bool = (fun uu____1945 -> (lookup_opt "warn_default_effects" as_bool))


let get_z3cliopt : Prims.unit  ->  Prims.string Prims.list = (fun uu____1951 -> (lookup_opt "z3cliopt" (as_list as_string)))


let get_z3refresh : Prims.unit  ->  Prims.bool = (fun uu____1957 -> (lookup_opt "z3refresh" as_bool))


let get_z3rlimit : Prims.unit  ->  Prims.int = (fun uu____1961 -> (lookup_opt "z3rlimit" as_int))


let get_z3rlimit_factor : Prims.unit  ->  Prims.int = (fun uu____1965 -> (lookup_opt "z3rlimit_factor" as_int))


let get_z3seed : Prims.unit  ->  Prims.int = (fun uu____1969 -> (lookup_opt "z3seed" as_int))


let get_no_positivity : Prims.unit  ->  Prims.bool = (fun uu____1973 -> (lookup_opt "__no_positivity" as_bool))


let get_ml_no_eta_expand_coertions : Prims.unit  ->  Prims.bool = (fun uu____1977 -> (lookup_opt "__ml_no_eta_expand_coertions" as_bool))


let dlevel : Prims.string  ->  debug_level_t = (fun uu___53_1981 -> (match (uu___53_1981) with
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
| Other (uu____1991) -> begin
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

let uu____1996 = (get_debug_level ())
in (FStar_All.pipe_right uu____1996 (FStar_Util.for_some (fun l1 -> (one_debug_level_geq (dlevel l1) l2))))))


let universe_include_path_base_dirs : Prims.string Prims.list = ("/ulib")::("/lib/fstar")::[]


let _version : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _platform : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _compiler : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _date : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _commit : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let display_version : Prims.unit  ->  Prims.unit = (fun uu____2088 -> (

let uu____2089 = (

let uu____2090 = (FStar_ST.op_Bang _version)
in (

let uu____2137 = (FStar_ST.op_Bang _platform)
in (

let uu____2184 = (FStar_ST.op_Bang _compiler)
in (

let uu____2231 = (FStar_ST.op_Bang _date)
in (

let uu____2278 = (FStar_ST.op_Bang _commit)
in (FStar_Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2090 uu____2137 uu____2184 uu____2231 uu____2278))))))
in (FStar_Util.print_string uu____2089)))


let display_usage_aux : 'Auu____2331 'Auu____2332 . ('Auu____2332 * Prims.string * 'Auu____2331 FStar_Getopt.opt_variant * Prims.string) Prims.list  ->  Prims.unit = (fun specs -> ((FStar_Util.print_string "fstar.exe [options] file[s]\n");
(FStar_List.iter (fun uu____2379 -> (match (uu____2379) with
| (uu____2390, flag, p, doc) -> begin
(match (p) with
| FStar_Getopt.ZeroArgs (ig) -> begin
(match ((Prims.op_Equality doc "")) with
| true -> begin
(

let uu____2401 = (

let uu____2402 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format1 "  --%s\n" uu____2402))
in (FStar_Util.print_string uu____2401))
end
| uu____2403 -> begin
(

let uu____2404 = (

let uu____2405 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format2 "  --%s  %s\n" uu____2405 doc))
in (FStar_Util.print_string uu____2404))
end)
end
| FStar_Getopt.OneArg (uu____2406, argname) -> begin
(match ((Prims.op_Equality doc "")) with
| true -> begin
(

let uu____2412 = (

let uu____2413 = (FStar_Util.colorize_bold flag)
in (

let uu____2414 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format2 "  --%s %s\n" uu____2413 uu____2414)))
in (FStar_Util.print_string uu____2412))
end
| uu____2415 -> begin
(

let uu____2416 = (

let uu____2417 = (FStar_Util.colorize_bold flag)
in (

let uu____2418 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format3 "  --%s %s  %s\n" uu____2417 uu____2418 doc)))
in (FStar_Util.print_string uu____2416))
end)
end)
end)) specs);
))


let mk_spec : (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant * Prims.string)  ->  FStar_Getopt.opt = (fun o -> (

let uu____2443 = o
in (match (uu____2443) with
| (ns, name, arg, desc) -> begin
(

let arg1 = (match (arg) with
| FStar_Getopt.ZeroArgs (f) -> begin
(

let g = (fun uu____2473 -> (

let uu____2474 = (f ())
in (set_option name uu____2474)))
in FStar_Getopt.ZeroArgs (g))
end
| FStar_Getopt.OneArg (f, d) -> begin
(

let g = (fun x -> (

let uu____2485 = (f x)
in (set_option name uu____2485)))
in FStar_Getopt.OneArg (((g), (d))))
end)
in ((ns), (name), (arg1), (desc)))
end)))


let accumulated_option : Prims.string  ->  option_val  ->  option_val = (fun name value -> (

let prev_values = (

let uu____2501 = (lookup_opt name (as_option as_list'))
in (FStar_Util.dflt [] uu____2501))
in (mk_list ((value)::prev_values))))


let reverse_accumulated_option : Prims.string  ->  option_val  ->  option_val = (fun name value -> (

let uu____2522 = (

let uu____2525 = (lookup_opt name as_list')
in (FStar_List.append uu____2525 ((value)::[])))
in (mk_list uu____2522)))


let accumulate_string : 'Auu____2538 . Prims.string  ->  ('Auu____2538  ->  Prims.string)  ->  'Auu____2538  ->  Prims.unit = (fun name post_processor value -> (

let uu____2556 = (

let uu____2557 = (

let uu____2558 = (post_processor value)
in (mk_string uu____2558))
in (accumulated_option name uu____2557))
in (set_option name uu____2556)))


let add_extract_module : Prims.string  ->  Prims.unit = (fun s -> (accumulate_string "extract_module" FStar_String.lowercase s))


let add_extract_namespace : Prims.string  ->  Prims.unit = (fun s -> (accumulate_string "extract_namespace" FStar_String.lowercase s))


let add_verify_module : Prims.string  ->  Prims.unit = (fun s -> (accumulate_string "verify_module" FStar_String.lowercase s))

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
| WithSideEffect of ((Prims.unit  ->  Prims.unit) * opt_type)


let uu___is_Const : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const (_0) -> begin
true
end
| uu____2640 -> begin
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
| uu____2654 -> begin
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
| uu____2667 -> begin
false
end))


let uu___is_PathStr : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PathStr (_0) -> begin
true
end
| uu____2673 -> begin
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
| uu____2687 -> begin
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
| uu____2703 -> begin
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
| uu____2729 -> begin
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
| uu____2767 -> begin
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
| uu____2799 -> begin
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
| uu____2813 -> begin
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
| uu____2833 -> begin
false
end))


let __proj__WithSideEffect__item___0 : opt_type  ->  ((Prims.unit  ->  Prims.unit) * opt_type) = (fun projectee -> (match (projectee) with
| WithSideEffect (_0) -> begin
_0
end))

exception InvalidArgument of (Prims.string)


let uu___is_InvalidArgument : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidArgument (uu____2867) -> begin
true
end
| uu____2868 -> begin
false
end))


let __proj__InvalidArgument__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidArgument (uu____2876) -> begin
uu____2876
end))


let rec parse_opt_val : Prims.string  ->  opt_type  ->  Prims.string  ->  option_val = (fun opt_name typ str_val -> (FStar_All.try_with (fun uu___56_2891 -> (match (()) with
| () -> begin
(match (typ) with
| Const (c) -> begin
c
end
| IntStr (uu____2893) -> begin
(

let uu____2894 = (FStar_Util.safe_int_of_string str_val)
in (match (uu____2894) with
| FStar_Pervasives_Native.Some (v1) -> begin
(mk_int v1)
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end))
end
| BoolStr -> begin
(

let uu____2898 = (match ((Prims.op_Equality str_val "true")) with
| true -> begin
true
end
| uu____2899 -> begin
(match ((Prims.op_Equality str_val "false")) with
| true -> begin
false
end
| uu____2900 -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end)
end)
in (mk_bool uu____2898))
end
| PathStr (uu____2901) -> begin
(mk_path str_val)
end
| SimpleStr (uu____2902) -> begin
(mk_string str_val)
end
| EnumStr (strs) -> begin
(match ((FStar_List.mem str_val strs)) with
| true -> begin
(mk_string str_val)
end
| uu____2906 -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end)
end
| OpenEnumStr (uu____2907) -> begin
(mk_string str_val)
end
| PostProcessed (pp, elem_spec) -> begin
(

let uu____2920 = (parse_opt_val opt_name elem_spec str_val)
in (pp uu____2920))
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
end)) (fun uu___55_2935 -> (match (uu___55_2935) with
| InvalidArgument (opt_name1) -> begin
(

let uu____2937 = (FStar_Util.format1 "Invalid argument to --%s" opt_name1)
in (failwith uu____2937))
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
| PostProcessed (uu____2971, elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| Accumulated (elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| ReverseAccumulated (elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| WithSideEffect (uu____2979, elem_spec) -> begin
(desc_of_opt_type elem_spec)
end)))


let rec arg_spec_of_opt_type : Prims.string  ->  opt_type  ->  option_val FStar_Getopt.opt_variant = (fun opt_name typ -> (

let parser = (parse_opt_val opt_name typ)
in (

let uu____3000 = (desc_of_opt_type typ)
in (match (uu____3000) with
| FStar_Pervasives_Native.None -> begin
FStar_Getopt.ZeroArgs ((fun uu____3006 -> (parser "")))
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

let uu____3020 = (

let uu____3021 = (as_string s)
in (FStar_String.lowercase uu____3021))
in (mk_string uu____3020)))


let rec specs_with_types : Prims.unit  ->  (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list = (fun uu____3038 -> (

let uu____3049 = (

let uu____3060 = (

let uu____3071 = (

let uu____3080 = (

let uu____3081 = (mk_bool true)
in Const (uu____3081))
in ((FStar_Getopt.noshort), ("cache_checked_modules"), (uu____3080), ("Write a \'.checked\' file for each module after verification and read from it if present, instead of re-verifying")))
in (

let uu____3082 = (

let uu____3093 = (

let uu____3104 = (

let uu____3115 = (

let uu____3126 = (

let uu____3137 = (

let uu____3148 = (

let uu____3157 = (

let uu____3158 = (mk_bool true)
in Const (uu____3158))
in ((FStar_Getopt.noshort), ("detail_errors"), (uu____3157), ("Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")))
in (

let uu____3159 = (

let uu____3170 = (

let uu____3179 = (

let uu____3180 = (mk_bool true)
in Const (uu____3180))
in ((FStar_Getopt.noshort), ("detail_hint_replay"), (uu____3179), ("Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")))
in (

let uu____3181 = (

let uu____3192 = (

let uu____3201 = (

let uu____3202 = (mk_bool true)
in Const (uu____3202))
in ((FStar_Getopt.noshort), ("doc"), (uu____3201), ("Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")))
in (

let uu____3203 = (

let uu____3214 = (

let uu____3225 = (

let uu____3234 = (

let uu____3235 = (mk_bool true)
in Const (uu____3235))
in ((FStar_Getopt.noshort), ("eager_inference"), (uu____3234), ("Solve all type-inference constraints eagerly; more efficient but at the cost of generality")))
in (

let uu____3236 = (

let uu____3247 = (

let uu____3256 = (

let uu____3257 = (mk_bool true)
in Const (uu____3257))
in ((FStar_Getopt.noshort), ("explicit_deps"), (uu____3256), ("Do not find dependencies automatically, the user provides them on the command-line")))
in (

let uu____3258 = (

let uu____3269 = (

let uu____3278 = (

let uu____3279 = (mk_bool true)
in Const (uu____3279))
in ((FStar_Getopt.noshort), ("extract_all"), (uu____3278), ("Discover the complete dependency graph and do not stop at interface boundaries")))
in (

let uu____3280 = (

let uu____3291 = (

let uu____3302 = (

let uu____3313 = (

let uu____3324 = (

let uu____3335 = (

let uu____3344 = (

let uu____3345 = (mk_bool true)
in Const (uu____3345))
in ((FStar_Getopt.noshort), ("hide_genident_nums"), (uu____3344), ("Don\'t print generated identifier numbers")))
in (

let uu____3346 = (

let uu____3357 = (

let uu____3366 = (

let uu____3367 = (mk_bool true)
in Const (uu____3367))
in ((FStar_Getopt.noshort), ("hide_uvar_nums"), (uu____3366), ("Don\'t print unification variable numbers")))
in (

let uu____3368 = (

let uu____3379 = (

let uu____3390 = (

let uu____3399 = (

let uu____3400 = (mk_bool true)
in Const (uu____3400))
in ((FStar_Getopt.noshort), ("hint_info"), (uu____3399), ("Print information regarding hints (deprecated; use --query_stats instead)")))
in (

let uu____3401 = (

let uu____3412 = (

let uu____3421 = (

let uu____3422 = (mk_bool true)
in Const (uu____3422))
in ((FStar_Getopt.noshort), ("in"), (uu____3421), ("Legacy interactive mode; reads input from stdin")))
in (

let uu____3423 = (

let uu____3434 = (

let uu____3443 = (

let uu____3444 = (mk_bool true)
in Const (uu____3444))
in ((FStar_Getopt.noshort), ("ide"), (uu____3443), ("JSON-based interactive mode for IDEs")))
in (

let uu____3445 = (

let uu____3456 = (

let uu____3467 = (

let uu____3476 = (

let uu____3477 = (mk_bool true)
in Const (uu____3477))
in ((FStar_Getopt.noshort), ("indent"), (uu____3476), ("Parses and outputs the files on the command line")))
in (

let uu____3478 = (

let uu____3489 = (

let uu____3500 = (

let uu____3511 = (

let uu____3520 = (

let uu____3521 = (mk_bool true)
in Const (uu____3521))
in ((FStar_Getopt.noshort), ("lax"), (uu____3520), ("Run the lax-type checker only (admit all verification conditions)")))
in (

let uu____3522 = (

let uu____3533 = (

let uu____3544 = (

let uu____3553 = (

let uu____3554 = (mk_bool true)
in Const (uu____3554))
in ((FStar_Getopt.noshort), ("log_types"), (uu____3553), ("Print types computed for data/val/let-bindings")))
in (

let uu____3555 = (

let uu____3566 = (

let uu____3575 = (

let uu____3576 = (mk_bool true)
in Const (uu____3576))
in ((FStar_Getopt.noshort), ("log_queries"), (uu____3575), ("Log the Z3 queries in several queries-*.smt2 files, as we go")))
in (

let uu____3577 = (

let uu____3588 = (

let uu____3599 = (

let uu____3610 = (

let uu____3621 = (

let uu____3630 = (

let uu____3631 = (mk_bool true)
in Const (uu____3631))
in ((FStar_Getopt.noshort), ("MLish"), (uu____3630), ("Trigger various specializations for compiling the F* compiler itself (not meant for user code)")))
in (

let uu____3632 = (

let uu____3643 = (

let uu____3654 = (

let uu____3663 = (

let uu____3664 = (mk_bool true)
in Const (uu____3664))
in ((FStar_Getopt.noshort), ("no_default_includes"), (uu____3663), ("Ignore the default module search paths")))
in (

let uu____3665 = (

let uu____3676 = (

let uu____3687 = (

let uu____3696 = (

let uu____3697 = (mk_bool true)
in Const (uu____3697))
in ((FStar_Getopt.noshort), ("no_location_info"), (uu____3696), ("Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")))
in (

let uu____3698 = (

let uu____3709 = (

let uu____3720 = (

let uu____3731 = (

let uu____3740 = (

let uu____3741 = (mk_bool true)
in Const (uu____3741))
in ((FStar_Getopt.noshort), ("print_bound_var_types"), (uu____3740), ("Print the types of bound variables")))
in (

let uu____3742 = (

let uu____3753 = (

let uu____3762 = (

let uu____3763 = (mk_bool true)
in Const (uu____3763))
in ((FStar_Getopt.noshort), ("print_effect_args"), (uu____3762), ("Print inferred predicate transformers for all computation types")))
in (

let uu____3764 = (

let uu____3775 = (

let uu____3784 = (

let uu____3785 = (mk_bool true)
in Const (uu____3785))
in ((FStar_Getopt.noshort), ("print_full_names"), (uu____3784), ("Print full names of variables")))
in (

let uu____3786 = (

let uu____3797 = (

let uu____3806 = (

let uu____3807 = (mk_bool true)
in Const (uu____3807))
in ((FStar_Getopt.noshort), ("print_implicits"), (uu____3806), ("Print implicit arguments")))
in (

let uu____3808 = (

let uu____3819 = (

let uu____3828 = (

let uu____3829 = (mk_bool true)
in Const (uu____3829))
in ((FStar_Getopt.noshort), ("print_universes"), (uu____3828), ("Print universes")))
in (

let uu____3830 = (

let uu____3841 = (

let uu____3850 = (

let uu____3851 = (mk_bool true)
in Const (uu____3851))
in ((FStar_Getopt.noshort), ("print_z3_statistics"), (uu____3850), ("Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")))
in (

let uu____3852 = (

let uu____3863 = (

let uu____3872 = (

let uu____3873 = (mk_bool true)
in Const (uu____3873))
in ((FStar_Getopt.noshort), ("prn"), (uu____3872), ("Print full names (deprecated; use --print_full_names instead)")))
in (

let uu____3874 = (

let uu____3885 = (

let uu____3894 = (

let uu____3895 = (mk_bool true)
in Const (uu____3895))
in ((FStar_Getopt.noshort), ("query_stats"), (uu____3894), ("Print SMT query statistics")))
in (

let uu____3896 = (

let uu____3907 = (

let uu____3916 = (

let uu____3917 = (mk_bool true)
in Const (uu____3917))
in ((FStar_Getopt.noshort), ("record_hints"), (uu____3916), ("Record a database of hints for efficient proof replay")))
in (

let uu____3918 = (

let uu____3929 = (

let uu____3940 = (

let uu____3951 = (

let uu____3960 = (

let uu____3961 = (mk_bool true)
in Const (uu____3961))
in ((FStar_Getopt.noshort), ("silent"), (uu____3960), (" ")))
in (

let uu____3962 = (

let uu____3973 = (

let uu____3984 = (

let uu____3995 = (

let uu____4006 = (

let uu____4017 = (

let uu____4028 = (

let uu____4037 = (

let uu____4038 = (mk_bool true)
in Const (uu____4038))
in ((FStar_Getopt.noshort), ("tactic_trace"), (uu____4037), ("Print a depth-indexed trace of tactic execution (Warning: very verbose)")))
in (

let uu____4039 = (

let uu____4050 = (

let uu____4061 = (

let uu____4070 = (

let uu____4071 = (mk_bool true)
in Const (uu____4071))
in ((FStar_Getopt.noshort), ("timing"), (uu____4070), ("Print the time it takes to verify each top-level definition")))
in (

let uu____4072 = (

let uu____4083 = (

let uu____4092 = (

let uu____4093 = (mk_bool true)
in Const (uu____4093))
in ((FStar_Getopt.noshort), ("trace_error"), (uu____4092), ("Don\'t print an error message; show an exception trace instead")))
in (

let uu____4094 = (

let uu____4105 = (

let uu____4114 = (

let uu____4115 = (mk_bool true)
in Const (uu____4115))
in ((FStar_Getopt.noshort), ("ugly"), (uu____4114), ("Emit output formatted for debugging")))
in (

let uu____4116 = (

let uu____4127 = (

let uu____4136 = (

let uu____4137 = (mk_bool true)
in Const (uu____4137))
in ((FStar_Getopt.noshort), ("unthrottle_inductives"), (uu____4136), ("Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")))
in (

let uu____4138 = (

let uu____4149 = (

let uu____4158 = (

let uu____4159 = (mk_bool true)
in Const (uu____4159))
in ((FStar_Getopt.noshort), ("unsafe_tactic_exec"), (uu____4158), ("Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")))
in (

let uu____4160 = (

let uu____4171 = (

let uu____4180 = (

let uu____4181 = (mk_bool true)
in Const (uu____4181))
in ((FStar_Getopt.noshort), ("use_eq_at_higher_order"), (uu____4180), ("Use equality constraints when comparing higher-order types (Temporary)")))
in (

let uu____4182 = (

let uu____4193 = (

let uu____4202 = (

let uu____4203 = (mk_bool true)
in Const (uu____4203))
in ((FStar_Getopt.noshort), ("use_hints"), (uu____4202), ("Use a previously recorded hints database for proof replay")))
in (

let uu____4204 = (

let uu____4215 = (

let uu____4226 = (

let uu____4235 = (

let uu____4236 = (mk_bool true)
in Const (uu____4236))
in ((FStar_Getopt.noshort), ("no_tactics"), (uu____4235), ("Do not run the tactic engine before discharging a VC")))
in (

let uu____4237 = (

let uu____4248 = (

let uu____4259 = (

let uu____4268 = (

let uu____4269 = (mk_bool true)
in Const (uu____4269))
in ((FStar_Getopt.noshort), ("verify_all"), (uu____4268), ("With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.")))
in (

let uu____4270 = (

let uu____4281 = (

let uu____4292 = (

let uu____4303 = (

let uu____4312 = (

let uu____4313 = (

let uu____4320 = (

let uu____4321 = (mk_bool true)
in Const (uu____4321))
in (((fun uu____4326 -> ((display_version ());
(FStar_All.exit (Prims.parse_int "0"));
))), (uu____4320)))
in WithSideEffect (uu____4313))
in ((118 (*v*)), ("version"), (uu____4312), ("Display version number")))
in (

let uu____4328 = (

let uu____4339 = (

let uu____4348 = (

let uu____4349 = (mk_bool true)
in Const (uu____4349))
in ((FStar_Getopt.noshort), ("warn_default_effects"), (uu____4348), ("Warn when (a -> b) is desugared to (a -> Tot b)")))
in (

let uu____4350 = (

let uu____4361 = (

let uu____4372 = (

let uu____4381 = (

let uu____4382 = (mk_bool true)
in Const (uu____4382))
in ((FStar_Getopt.noshort), ("z3refresh"), (uu____4381), ("Restart Z3 after each query; useful for ensuring proof robustness")))
in (

let uu____4383 = (

let uu____4394 = (

let uu____4405 = (

let uu____4416 = (

let uu____4427 = (

let uu____4436 = (

let uu____4437 = (mk_bool true)
in Const (uu____4437))
in ((FStar_Getopt.noshort), ("__no_positivity"), (uu____4436), ("Don\'t check positivity of inductive types")))
in (

let uu____4438 = (

let uu____4449 = (

let uu____4458 = (

let uu____4459 = (mk_bool true)
in Const (uu____4459))
in ((FStar_Getopt.noshort), ("__ml_no_eta_expand_coertions"), (uu____4458), ("Do not eta-expand coertions in generated OCaml")))
in (

let uu____4460 = (

let uu____4471 = (

let uu____4480 = (

let uu____4481 = (

let uu____4488 = (

let uu____4489 = (mk_bool true)
in Const (uu____4489))
in (((fun uu____4494 -> ((

let uu____4496 = (specs ())
in (display_usage_aux uu____4496));
(FStar_All.exit (Prims.parse_int "0"));
))), (uu____4488)))
in WithSideEffect (uu____4481))
in ((104 (*h*)), ("help"), (uu____4480), ("Display this information")))
in (uu____4471)::[])
in (uu____4449)::uu____4460))
in (uu____4427)::uu____4438))
in (((FStar_Getopt.noshort), ("z3seed"), (IntStr ("positive_integer")), ("Set the Z3 random seed (default 0)")))::uu____4416)
in (((FStar_Getopt.noshort), ("z3rlimit_factor"), (IntStr ("positive_integer")), ("Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")))::uu____4405)
in (((FStar_Getopt.noshort), ("z3rlimit"), (IntStr ("positive_integer")), ("Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")))::uu____4394)
in (uu____4372)::uu____4383))
in (((FStar_Getopt.noshort), ("z3cliopt"), (ReverseAccumulated (SimpleStr ("option"))), ("Z3 command line options")))::uu____4361)
in (uu____4339)::uu____4350))
in (uu____4303)::uu____4328))
in (((FStar_Getopt.noshort), ("__temp_no_proj"), (Accumulated (SimpleStr ("module_name"))), ("Don\'t generate projectors for this module")))::uu____4292)
in (((FStar_Getopt.noshort), ("verify_module"), (Accumulated (PostProcessed (((pp_lowercase), (SimpleStr ("module_name")))))), ("Name of the module to verify")))::uu____4281)
in (uu____4259)::uu____4270))
in (((FStar_Getopt.noshort), ("using_facts_from"), (WithSideEffect ((((fun uu____4635 -> (

let uu____4636 = (mk_bool true)
in (set_option "z3refresh" uu____4636)))), (Accumulated (SimpleStr ("namespace | fact id")))))), ("Implies --z3refresh; prunes the context to include facts from the given namespace of fact id (multiple uses of this option will prune the context to include those facts that match any of the provided namespaces / fact ids")))::uu____4248)
in (uu____4226)::uu____4237))
in (((FStar_Getopt.noshort), ("use_native_tactics"), (PathStr ("path")), ("Use compiled tactics from <path>")))::uu____4215)
in (uu____4193)::uu____4204))
in (uu____4171)::uu____4182))
in (uu____4149)::uu____4160))
in (uu____4127)::uu____4138))
in (uu____4105)::uu____4116))
in (uu____4083)::uu____4094))
in (uu____4061)::uu____4072))
in (((FStar_Getopt.noshort), ("tactic_trace_d"), (IntStr ("positive_integer")), ("Trace tactics up to a certain binding depth")))::uu____4050)
in (uu____4028)::uu____4039))
in (((FStar_Getopt.noshort), ("split_cases"), (IntStr ("positive_integer")), ("Partition VC of a match into groups of <positive_integer> cases")))::uu____4017)
in (((FStar_Getopt.noshort), ("smtencoding.l_arith_repr"), (EnumStr (("native")::("boxwrap")::[])), ("Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if \'boxwrap\', use \'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus\'; \n\t\tif \'native\', use \'+, -, -\'; \n\t\t(default \'boxwrap\')")))::uu____4006)
in (((FStar_Getopt.noshort), ("smtencoding.nl_arith_repr"), (EnumStr (("native")::("wrapped")::("boxwrap")::[])), ("Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if \'boxwrap\' use \'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus\'; \n\t\tif \'native\' use \'*, div, mod\';\n\t\tif \'wrapped\' use \'_mul, _div, _mod : Int*Int -> Int\'; \n\t\t(default \'boxwrap\')")))::uu____3995)
in (((FStar_Getopt.noshort), ("smtencoding.elim_box"), (BoolStr), ("Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default \'false\')")))::uu____3984)
in (((FStar_Getopt.noshort), ("smt"), (PathStr ("path")), ("Path to the Z3 SMT solver (we could eventually support other solvers)")))::uu____3973)
in (uu____3951)::uu____3962))
in (((FStar_Getopt.noshort), ("show_signatures"), (Accumulated (SimpleStr ("module_name"))), ("Show the checked signatures for all top-level symbols in the module")))::uu____3940)
in (((FStar_Getopt.noshort), ("reuse_hint_for"), (SimpleStr ("toplevel_name")), ("Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term \'g\'")))::uu____3929)
in (uu____3907)::uu____3918))
in (uu____3885)::uu____3896))
in (uu____3863)::uu____3874))
in (uu____3841)::uu____3852))
in (uu____3819)::uu____3830))
in (uu____3797)::uu____3808))
in (uu____3775)::uu____3786))
in (uu____3753)::uu____3764))
in (uu____3731)::uu____3742))
in (((FStar_Getopt.noshort), ("prims"), (PathStr ("file")), ("")))::uu____3720)
in (((FStar_Getopt.noshort), ("odir"), (PostProcessed (((pp_validate_dir), (PathStr ("dir"))))), ("Place output in directory <dir>")))::uu____3709)
in (uu____3687)::uu____3698))
in (((FStar_Getopt.noshort), ("no_extract"), (Accumulated (PathStr ("module name"))), ("Do not extract code from this module")))::uu____3676)
in (uu____3654)::uu____3665))
in (((FStar_Getopt.noshort), ("n_cores"), (IntStr ("positive_integer")), ("Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")))::uu____3643)
in (uu____3621)::uu____3632))
in (((FStar_Getopt.noshort), ("min_fuel"), (IntStr ("non-negative integer")), ("Minimum number of unrolling of recursive functions to try (default 1)")))::uu____3610)
in (((FStar_Getopt.noshort), ("max_ifuel"), (IntStr ("non-negative integer")), ("Number of unrolling of inductive datatypes to try at most (default 2)")))::uu____3599)
in (((FStar_Getopt.noshort), ("max_fuel"), (IntStr ("non-negative integer")), ("Number of unrolling of recursive functions to try at most (default 8)")))::uu____3588)
in (uu____3566)::uu____3577))
in (uu____3544)::uu____3555))
in (((FStar_Getopt.noshort), ("load"), (ReverseAccumulated (PathStr ("module"))), ("Load compiled module")))::uu____3533)
in (uu____3511)::uu____3522))
in (((FStar_Getopt.noshort), ("initial_ifuel"), (IntStr ("non-negative integer")), ("Number of unrolling of inductive datatypes to try at first (default 1)")))::uu____3500)
in (((FStar_Getopt.noshort), ("initial_fuel"), (IntStr ("non-negative integer")), ("Number of unrolling of recursive functions to try initially (default 2)")))::uu____3489)
in (uu____3467)::uu____3478))
in (((FStar_Getopt.noshort), ("include"), (ReverseAccumulated (PathStr ("path"))), ("A directory in which to search for files included on the command line")))::uu____3456)
in (uu____3434)::uu____3445))
in (uu____3412)::uu____3423))
in (uu____3390)::uu____3401))
in (((FStar_Getopt.noshort), ("hint_file"), (PathStr ("path")), ("Read/write hints to <path> (instead of module-specific hints files)")))::uu____3379)
in (uu____3357)::uu____3368))
in (uu____3335)::uu____3346))
in (((FStar_Getopt.noshort), ("gen_native_tactics"), (PathStr ("[path]")), ("Compile all user tactics used in the module in <path>")))::uu____3324)
in (((FStar_Getopt.noshort), ("fstar_home"), (PathStr ("dir")), ("Set the FSTAR_HOME variable to <dir>")))::uu____3313)
in (((FStar_Getopt.noshort), ("extract_namespace"), (Accumulated (PostProcessed (((pp_lowercase), (SimpleStr ("namespace name")))))), ("Only extract modules in the specified namespace")))::uu____3302)
in (((FStar_Getopt.noshort), ("extract_module"), (Accumulated (PostProcessed (((pp_lowercase), (SimpleStr ("module_name")))))), ("Only extract the specified modules (instead of the possibly-partial dependency graph)")))::uu____3291)
in (uu____3269)::uu____3280))
in (uu____3247)::uu____3258))
in (uu____3225)::uu____3236))
in (((FStar_Getopt.noshort), ("dump_module"), (Accumulated (SimpleStr ("module_name"))), ("")))::uu____3214)
in (uu____3192)::uu____3203))
in (uu____3170)::uu____3181))
in (uu____3148)::uu____3159))
in (((FStar_Getopt.noshort), ("dep"), (EnumStr (("make")::("graph")::[])), ("Output the transitive closure of the dependency graph in a format suitable for the given tool")))::uu____3137)
in (((FStar_Getopt.noshort), ("debug_level"), (Accumulated (OpenEnumStr (((("Low")::("Medium")::("High")::("Extreme")::[]), ("..."))))), ("Control the verbosity of debugging info")))::uu____3126)
in (((FStar_Getopt.noshort), ("debug"), (Accumulated (SimpleStr ("module_name"))), ("Print lots of debugging information while checking module")))::uu____3115)
in (((FStar_Getopt.noshort), ("codegen-lib"), (Accumulated (SimpleStr ("namespace"))), ("External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")))::uu____3104)
in (((FStar_Getopt.noshort), ("codegen"), (EnumStr (("OCaml")::("FSharp")::("Kremlin")::[])), ("Generate code for execution")))::uu____3093)
in (uu____3071)::uu____3082))
in (((FStar_Getopt.noshort), ("admit_except"), (SimpleStr ("(symbol, id)")), ("Admit all verification conditions, except those with query label (<symbol>, <id>)) (e.g. --admit_except \'(FStar.Fin.pigeonhole, 1)\'")))::uu____3060)
in (((FStar_Getopt.noshort), ("admit_smt_queries"), (BoolStr), ("Admit SMT queries, unsafe! (default \'false\')")))::uu____3049))
and specs : Prims.unit  ->  FStar_Getopt.opt Prims.list = (fun uu____5213 -> (

let uu____5216 = (specs_with_types ())
in (FStar_List.map (fun uu____5241 -> (match (uu____5241) with
| (short, long, typ, doc) -> begin
(

let uu____5254 = (

let uu____5265 = (arg_spec_of_opt_type long typ)
in ((short), (long), (uu____5265), (doc)))
in (mk_spec uu____5254))
end)) uu____5216)))


let settable : Prims.string  ->  Prims.bool = (fun uu___54_5273 -> (match (uu___54_5273) with
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
| "detail_errors" -> begin
true
end
| "detail_hint_replay" -> begin
true
end
| "eager_inference" -> begin
true
end
| "hide_genident_nums" -> begin
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
| "show_signatures" -> begin
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
| "split_cases" -> begin
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
| "tactic_trace" -> begin
true
end
| "tactic_trace_d" -> begin
true
end
| "using_facts_from" -> begin
true
end
| "__temp_no_proj" -> begin
true
end
| "reuse_hint_for" -> begin
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
| uu____5274 -> begin
false
end))


let resettable : Prims.string  ->  Prims.bool = (fun s -> (((settable s) || (Prims.op_Equality s "z3seed")) || (Prims.op_Equality s "z3cliopt")))


let all_specs : FStar_Getopt.opt Prims.list = (specs ())


let all_specs_with_types : (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list = (specs_with_types ())


let settable_specs : (FStar_BaseTypes.char * Prims.string * Prims.unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____5332 -> (match (uu____5332) with
| (uu____5343, x, uu____5345, uu____5346) -> begin
(settable x)
end))))


let resettable_specs : (FStar_BaseTypes.char * Prims.string * Prims.unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____5392 -> (match (uu____5392) with
| (uu____5403, x, uu____5405, uu____5406) -> begin
(resettable x)
end))))


let display_usage : Prims.unit  ->  Prims.unit = (fun uu____5414 -> (

let uu____5415 = (specs ())
in (display_usage_aux uu____5415)))


let fstar_home : Prims.unit  ->  Prims.string = (fun uu____5431 -> (

let uu____5432 = (get_fstar_home ())
in (match (uu____5432) with
| FStar_Pervasives_Native.None -> begin
(

let x = (FStar_Util.get_exec_dir ())
in (

let x1 = (Prims.strcat x "/..")
in ((

let uu____5438 = (

let uu____5443 = (mk_string x1)
in (("fstar_home"), (uu____5443)))
in (set_option' uu____5438));
x1;
)))
end
| FStar_Pervasives_Native.Some (x) -> begin
x
end)))

exception File_argument of (Prims.string)


let uu___is_File_argument : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| File_argument (uu____5452) -> begin
true
end
| uu____5453 -> begin
false
end))


let __proj__File_argument__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| File_argument (uu____5461) -> begin
uu____5461
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
in (FStar_All.try_with (fun uu___58_5496 -> (match (()) with
| () -> begin
(match ((Prims.op_Equality s "")) with
| true -> begin
FStar_Getopt.Success
end
| uu____5497 -> begin
(FStar_Getopt.parse_string specs1 (fun s1 -> (FStar_Exn.raise (File_argument (s1)))) s)
end)
end)) (fun uu___57_5505 -> (match (uu___57_5505) with
| File_argument (s1) -> begin
(

let uu____5507 = (FStar_Util.format1 "File %s is not a valid option" s1)
in FStar_Getopt.Error (uu____5507))
end)))))


let file_list_ : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let parse_cmd_line : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____5530 -> (

let res = (FStar_Getopt.parse_cmdline all_specs (fun i -> (

let uu____5535 = (

let uu____5538 = (FStar_ST.op_Bang file_list_)
in (FStar_List.append uu____5538 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list_ uu____5535))))
in (

let uu____5641 = (

let uu____5644 = (FStar_ST.op_Bang file_list_)
in (FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5644))
in ((res), (uu____5641)))))


let file_list : Prims.unit  ->  Prims.string Prims.list = (fun uu____5704 -> (FStar_ST.op_Bang file_list_))


let restore_cmd_line_options : Prims.bool  ->  FStar_Getopt.parse_cmdline_res = (fun should_clear -> (

let old_verify_module = (get_verify_module ())
in ((match (should_clear) with
| true -> begin
(clear ())
end
| uu____5763 -> begin
(init ())
end);
(

let r = (

let uu____5765 = (specs ())
in (FStar_Getopt.parse_cmdline uu____5765 (fun x -> ())))
in ((

let uu____5771 = (

let uu____5776 = (

let uu____5777 = (FStar_List.map mk_string old_verify_module)
in List (uu____5777))
in (("verify_module"), (uu____5776)))
in (set_option' uu____5771));
r;
));
)))


let module_name_of_file_name : Prims.string  ->  Prims.string = (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let f2 = (

let uu____5786 = (

let uu____5787 = (

let uu____5788 = (

let uu____5789 = (FStar_Util.get_file_extension f1)
in (FStar_String.length uu____5789))
in ((FStar_String.length f1) - uu____5788))
in (uu____5787 - (Prims.parse_int "1")))
in (FStar_String.substring f1 (Prims.parse_int "0") uu____5786))
in (FStar_String.lowercase f2))))


let should_verify : Prims.string  ->  Prims.bool = (fun m -> (

let uu____5794 = (get_lax ())
in (match (uu____5794) with
| true -> begin
false
end
| uu____5795 -> begin
(

let uu____5796 = (get_verify_all ())
in (match (uu____5796) with
| true -> begin
true
end
| uu____5797 -> begin
(

let uu____5798 = (get_verify_module ())
in (match (uu____5798) with
| [] -> begin
(

let uu____5801 = (file_list ())
in (FStar_List.existsML (fun f -> (

let uu____5807 = (module_name_of_file_name f)
in (Prims.op_Equality uu____5807 m))) uu____5801))
end
| l -> begin
(FStar_List.contains (FStar_String.lowercase m) l)
end))
end))
end)))


let should_verify_file : Prims.string  ->  Prims.bool = (fun fn -> (

let uu____5815 = (module_name_of_file_name fn)
in (should_verify uu____5815)))


let dont_gen_projectors : Prims.string  ->  Prims.bool = (fun m -> (

let uu____5820 = (get___temp_no_proj ())
in (FStar_List.contains m uu____5820)))


let should_print_message : Prims.string  ->  Prims.bool = (fun m -> (

let uu____5827 = (should_verify m)
in (match (uu____5827) with
| true -> begin
(Prims.op_disEquality m "Prims")
end
| uu____5828 -> begin
false
end)))


let include_path : Prims.unit  ->  Prims.string Prims.list = (fun uu____5834 -> (

let uu____5835 = (get_no_default_includes ())
in (match (uu____5835) with
| true -> begin
(get_include ())
end
| uu____5838 -> begin
(

let h = (fstar_home ())
in (

let defs = universe_include_path_base_dirs
in (

let uu____5843 = (

let uu____5846 = (FStar_All.pipe_right defs (FStar_List.map (fun x -> (Prims.strcat h x))))
in (FStar_All.pipe_right uu____5846 (FStar_List.filter FStar_Util.file_exists)))
in (

let uu____5859 = (

let uu____5862 = (get_include ())
in (FStar_List.append uu____5862 ((".")::[])))
in (FStar_List.append uu____5843 uu____5859)))))
end)))


let find_file : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun filename -> (

let uu____5871 = (FStar_Util.is_path_absolute filename)
in (match (uu____5871) with
| true -> begin
(match ((FStar_Util.file_exists filename)) with
| true -> begin
FStar_Pervasives_Native.Some (filename)
end
| uu____5876 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____5877 -> begin
(

let uu____5878 = (

let uu____5881 = (include_path ())
in (FStar_List.rev uu____5881))
in (FStar_Util.find_map uu____5878 (fun p -> (

let path = (FStar_Util.join_paths p filename)
in (match ((FStar_Util.file_exists path)) with
| true -> begin
FStar_Pervasives_Native.Some (path)
end
| uu____5890 -> begin
FStar_Pervasives_Native.None
end)))))
end)))


let prims : Prims.unit  ->  Prims.string = (fun uu____5894 -> (

let uu____5895 = (get_prims ())
in (match (uu____5895) with
| FStar_Pervasives_Native.None -> begin
(

let filename = "prims.fst"
in (

let uu____5899 = (find_file filename)
in (match (uu____5899) with
| FStar_Pervasives_Native.Some (result) -> begin
result
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5903 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____5903))
end)))
end
| FStar_Pervasives_Native.Some (x) -> begin
x
end)))


let prims_basename : Prims.unit  ->  Prims.string = (fun uu____5908 -> (

let uu____5909 = (prims ())
in (FStar_Util.basename uu____5909)))


let pervasives : Prims.unit  ->  Prims.string = (fun uu____5913 -> (

let filename = "FStar.Pervasives.fst"
in (

let uu____5915 = (find_file filename)
in (match (uu____5915) with
| FStar_Pervasives_Native.Some (result) -> begin
result
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5919 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____5919))
end))))


let pervasives_basename : Prims.unit  ->  Prims.string = (fun uu____5923 -> (

let uu____5924 = (pervasives ())
in (FStar_Util.basename uu____5924)))


let pervasives_native_basename : Prims.unit  ->  Prims.string = (fun uu____5928 -> (

let filename = "FStar.Pervasives.Native.fst"
in (

let uu____5930 = (find_file filename)
in (match (uu____5930) with
| FStar_Pervasives_Native.Some (result) -> begin
(FStar_Util.basename result)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5934 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____5934))
end))))


let prepend_output_dir : Prims.string  ->  Prims.string = (fun fname -> (

let uu____5939 = (get_odir ())
in (match (uu____5939) with
| FStar_Pervasives_Native.None -> begin
fname
end
| FStar_Pervasives_Native.Some (x) -> begin
(Prims.strcat x (Prims.strcat "/" fname))
end)))


let __temp_no_proj : Prims.string  ->  Prims.bool = (fun s -> (

let uu____5947 = (get___temp_no_proj ())
in (FStar_All.pipe_right uu____5947 (FStar_List.contains s))))


let admit_smt_queries : Prims.unit  ->  Prims.bool = (fun uu____5955 -> (get_admit_smt_queries ()))


let admit_except : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____5961 -> (get_admit_except ()))


let cache_checked_modules : Prims.unit  ->  Prims.bool = (fun uu____5965 -> (get_cache_checked_modules ()))


let codegen : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____5971 -> (get_codegen ()))


let codegen_libs : Prims.unit  ->  Prims.string Prims.list Prims.list = (fun uu____5979 -> (

let uu____5980 = (get_codegen_lib ())
in (FStar_All.pipe_right uu____5980 (FStar_List.map (fun x -> (FStar_Util.split x "."))))))


let debug_any : Prims.unit  ->  Prims.bool = (fun uu____5996 -> (

let uu____5997 = (get_debug ())
in (Prims.op_disEquality uu____5997 [])))


let debug_at_level : Prims.string  ->  debug_level_t  ->  Prims.bool = (fun modul level -> ((

let uu____6012 = (get_debug ())
in (FStar_All.pipe_right uu____6012 (FStar_List.contains modul))) && (debug_level_geq level)))


let dep : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6022 -> (get_dep ()))


let detail_errors : Prims.unit  ->  Prims.bool = (fun uu____6026 -> (get_detail_errors ()))


let detail_hint_replay : Prims.unit  ->  Prims.bool = (fun uu____6030 -> (get_detail_hint_replay ()))


let doc : Prims.unit  ->  Prims.bool = (fun uu____6034 -> (get_doc ()))


let dump_module : Prims.string  ->  Prims.bool = (fun s -> (

let uu____6039 = (get_dump_module ())
in (FStar_All.pipe_right uu____6039 (FStar_List.contains s))))


let eager_inference : Prims.unit  ->  Prims.bool = (fun uu____6047 -> (get_eager_inference ()))


let explicit_deps : Prims.unit  ->  Prims.bool = (fun uu____6051 -> (get_explicit_deps ()))


let extract_all : Prims.unit  ->  Prims.bool = (fun uu____6055 -> (get_extract_all ()))


let fs_typ_app : Prims.string  ->  Prims.bool = (fun filename -> (

let uu____6060 = (FStar_ST.op_Bang light_off_files)
in (FStar_List.contains filename uu____6060)))


let gen_native_tactics : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6118 -> (get_gen_native_tactics ()))


let full_context_dependency : Prims.unit  ->  Prims.bool = (fun uu____6122 -> true)


let hide_genident_nums : Prims.unit  ->  Prims.bool = (fun uu____6126 -> (get_hide_genident_nums ()))


let hide_uvar_nums : Prims.unit  ->  Prims.bool = (fun uu____6130 -> (get_hide_uvar_nums ()))


let hint_info : Prims.unit  ->  Prims.bool = (fun uu____6134 -> ((get_hint_info ()) || (get_query_stats ())))


let hint_file : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6140 -> (get_hint_file ()))


let ide : Prims.unit  ->  Prims.bool = (fun uu____6144 -> (get_ide ()))


let indent : Prims.unit  ->  Prims.bool = (fun uu____6148 -> (get_indent ()))


let initial_fuel : Prims.unit  ->  Prims.int = (fun uu____6152 -> (

let uu____6153 = (get_initial_fuel ())
in (

let uu____6154 = (get_max_fuel ())
in (Prims.min uu____6153 uu____6154))))


let initial_ifuel : Prims.unit  ->  Prims.int = (fun uu____6158 -> (

let uu____6159 = (get_initial_ifuel ())
in (

let uu____6160 = (get_max_ifuel ())
in (Prims.min uu____6159 uu____6160))))


let interactive : Prims.unit  ->  Prims.bool = (fun uu____6164 -> ((get_in ()) || (get_ide ())))


let lax : Prims.unit  ->  Prims.bool = (fun uu____6168 -> (get_lax ()))


let load : Prims.unit  ->  Prims.string Prims.list = (fun uu____6174 -> (get_load ()))


let legacy_interactive : Prims.unit  ->  Prims.bool = (fun uu____6178 -> (get_in ()))


let log_queries : Prims.unit  ->  Prims.bool = (fun uu____6182 -> (get_log_queries ()))


let log_types : Prims.unit  ->  Prims.bool = (fun uu____6186 -> (get_log_types ()))


let max_fuel : Prims.unit  ->  Prims.int = (fun uu____6190 -> (get_max_fuel ()))


let max_ifuel : Prims.unit  ->  Prims.int = (fun uu____6194 -> (get_max_ifuel ()))


let min_fuel : Prims.unit  ->  Prims.int = (fun uu____6198 -> (get_min_fuel ()))


let ml_ish : Prims.unit  ->  Prims.bool = (fun uu____6202 -> (get_MLish ()))


let set_ml_ish : Prims.unit  ->  Prims.unit = (fun uu____6206 -> (set_option "MLish" (Bool (true))))


let n_cores : Prims.unit  ->  Prims.int = (fun uu____6210 -> (get_n_cores ()))


let no_default_includes : Prims.unit  ->  Prims.bool = (fun uu____6214 -> (get_no_default_includes ()))


let no_extract : Prims.string  ->  Prims.bool = (fun s -> (

let uu____6219 = (get_no_extract ())
in (FStar_All.pipe_right uu____6219 (FStar_List.contains s))))


let no_location_info : Prims.unit  ->  Prims.bool = (fun uu____6227 -> (get_no_location_info ()))


let output_dir : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6233 -> (get_odir ()))


let ugly : Prims.unit  ->  Prims.bool = (fun uu____6237 -> (get_ugly ()))


let print_bound_var_types : Prims.unit  ->  Prims.bool = (fun uu____6241 -> (get_print_bound_var_types ()))


let print_effect_args : Prims.unit  ->  Prims.bool = (fun uu____6245 -> (get_print_effect_args ()))


let print_implicits : Prims.unit  ->  Prims.bool = (fun uu____6249 -> (get_print_implicits ()))


let print_real_names : Prims.unit  ->  Prims.bool = (fun uu____6253 -> ((get_prn ()) || (get_print_full_names ())))


let print_universes : Prims.unit  ->  Prims.bool = (fun uu____6257 -> (get_print_universes ()))


let print_z3_statistics : Prims.unit  ->  Prims.bool = (fun uu____6261 -> ((get_print_z3_statistics ()) || (get_query_stats ())))


let query_stats : Prims.unit  ->  Prims.bool = (fun uu____6265 -> (get_query_stats ()))


let record_hints : Prims.unit  ->  Prims.bool = (fun uu____6269 -> (get_record_hints ()))


let reuse_hint_for : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6275 -> (get_reuse_hint_for ()))


let silent : Prims.unit  ->  Prims.bool = (fun uu____6279 -> (get_silent ()))


let smtencoding_elim_box : Prims.unit  ->  Prims.bool = (fun uu____6283 -> (get_smtencoding_elim_box ()))


let smtencoding_nl_arith_native : Prims.unit  ->  Prims.bool = (fun uu____6287 -> (

let uu____6288 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____6288 "native")))


let smtencoding_nl_arith_wrapped : Prims.unit  ->  Prims.bool = (fun uu____6292 -> (

let uu____6293 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____6293 "wrapped")))


let smtencoding_nl_arith_default : Prims.unit  ->  Prims.bool = (fun uu____6297 -> (

let uu____6298 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____6298 "boxwrap")))


let smtencoding_l_arith_native : Prims.unit  ->  Prims.bool = (fun uu____6302 -> (

let uu____6303 = (get_smtencoding_l_arith_repr ())
in (Prims.op_Equality uu____6303 "native")))


let smtencoding_l_arith_default : Prims.unit  ->  Prims.bool = (fun uu____6307 -> (

let uu____6308 = (get_smtencoding_l_arith_repr ())
in (Prims.op_Equality uu____6308 "boxwrap")))


let split_cases : Prims.unit  ->  Prims.int = (fun uu____6312 -> (get_split_cases ()))


let tactic_trace : Prims.unit  ->  Prims.bool = (fun uu____6316 -> (get_tactic_trace ()))


let tactic_trace_d : Prims.unit  ->  Prims.int = (fun uu____6320 -> (get_tactic_trace_d ()))


let timing : Prims.unit  ->  Prims.bool = (fun uu____6324 -> (get_timing ()))


let trace_error : Prims.unit  ->  Prims.bool = (fun uu____6328 -> (get_trace_error ()))


let unthrottle_inductives : Prims.unit  ->  Prims.bool = (fun uu____6332 -> (get_unthrottle_inductives ()))


let unsafe_tactic_exec : Prims.unit  ->  Prims.bool = (fun uu____6336 -> (get_unsafe_tactic_exec ()))


let use_eq_at_higher_order : Prims.unit  ->  Prims.bool = (fun uu____6340 -> (get_use_eq_at_higher_order ()))


let use_hints : Prims.unit  ->  Prims.bool = (fun uu____6344 -> (get_use_hints ()))


let use_native_tactics : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____6350 -> (get_use_native_tactics ()))


let use_tactics : Prims.unit  ->  Prims.bool = (fun uu____6354 -> (get_use_tactics ()))


let using_facts_from : Prims.unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____6362 -> (get_using_facts_from ()))


let verify_all : Prims.unit  ->  Prims.bool = (fun uu____6366 -> (get_verify_all ()))


let verify_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____6372 -> (get_verify_module ()))


let warn_default_effects : Prims.unit  ->  Prims.bool = (fun uu____6376 -> (get_warn_default_effects ()))


let z3_exe : Prims.unit  ->  Prims.string = (fun uu____6380 -> (

let uu____6381 = (get_smt ())
in (match (uu____6381) with
| FStar_Pervasives_Native.None -> begin
(FStar_Platform.exe "z3")
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let z3_cliopt : Prims.unit  ->  Prims.string Prims.list = (fun uu____6390 -> (get_z3cliopt ()))


let z3_refresh : Prims.unit  ->  Prims.bool = (fun uu____6394 -> (get_z3refresh ()))


let z3_rlimit : Prims.unit  ->  Prims.int = (fun uu____6398 -> (get_z3rlimit ()))


let z3_rlimit_factor : Prims.unit  ->  Prims.int = (fun uu____6402 -> (get_z3rlimit_factor ()))


let z3_seed : Prims.unit  ->  Prims.int = (fun uu____6406 -> (get_z3seed ()))


let no_positivity : Prims.unit  ->  Prims.bool = (fun uu____6410 -> (get_no_positivity ()))


let ml_no_eta_expand_coertions : Prims.unit  ->  Prims.bool = (fun uu____6414 -> (get_ml_no_eta_expand_coertions ()))


let should_extract : Prims.string  ->  Prims.bool = (fun m -> ((

let uu____6421 = (no_extract m)
in (not (uu____6421))) && ((extract_all ()) || (

let uu____6424 = (get_extract_module ())
in (match (uu____6424) with
| [] -> begin
(

let uu____6427 = (get_extract_namespace ())
in (match (uu____6427) with
| [] -> begin
true
end
| ns -> begin
(FStar_Util.for_some (FStar_Util.starts_with (FStar_String.lowercase m)) ns)
end))
end
| l -> begin
(FStar_List.contains (FStar_String.lowercase m) l)
end)))))




