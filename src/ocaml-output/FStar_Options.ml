
open Prims
open FStar_Pervasives

let debug_embedding : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let eager_embedding : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)

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
| uu____26 -> begin
false
end))


let uu___is_Medium : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Medium -> begin
true
end
| uu____37 -> begin
false
end))


let uu___is_High : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| High -> begin
true
end
| uu____48 -> begin
false
end))


let uu___is_Extreme : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Extreme -> begin
true
end
| uu____59 -> begin
false
end))


let uu___is_Other : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Other (_0) -> begin
true
end
| uu____72 -> begin
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
| uu____126 -> begin
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
| uu____149 -> begin
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
| uu____172 -> begin
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
| uu____195 -> begin
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
| uu____219 -> begin
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
| uu____243 -> begin
false
end))

type options =
| Set
| Reset
| Restore


let uu___is_Set : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Set -> begin
true
end
| uu____254 -> begin
false
end))


let uu___is_Reset : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reset -> begin
true
end
| uu____265 -> begin
false
end))


let uu___is_Restore : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Restore -> begin
true
end
| uu____276 -> begin
false
end))

type error_flag =
| CFatal
| CAlwaysError
| CError
| CWarning
| CSilent


let uu___is_CFatal : error_flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CFatal -> begin
true
end
| uu____287 -> begin
false
end))


let uu___is_CAlwaysError : error_flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CAlwaysError -> begin
true
end
| uu____298 -> begin
false
end))


let uu___is_CError : error_flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CError -> begin
true
end
| uu____309 -> begin
false
end))


let uu___is_CWarning : error_flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CWarning -> begin
true
end
| uu____320 -> begin
false
end))


let uu___is_CSilent : error_flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CSilent -> begin
true
end
| uu____331 -> begin
false
end))


let __unit_tests__ : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let __unit_tests : unit  ->  Prims.bool = (fun uu____345 -> (FStar_ST.op_Bang __unit_tests__))


let __set_unit_tests : unit  ->  unit = (fun uu____372 -> (FStar_ST.op_Colon_Equals __unit_tests__ true))


let __clear_unit_tests : unit  ->  unit = (fun uu____400 -> (FStar_ST.op_Colon_Equals __unit_tests__ false))


let as_bool : option_val  ->  Prims.bool = (fun uu___0_429 -> (match (uu___0_429) with
| Bool (b) -> begin
b
end
| uu____433 -> begin
(failwith "Impos: expected Bool")
end))


let as_int : option_val  ->  Prims.int = (fun uu___1_442 -> (match (uu___1_442) with
| Int (b) -> begin
b
end
| uu____446 -> begin
(failwith "Impos: expected Int")
end))


let as_string : option_val  ->  Prims.string = (fun uu___2_455 -> (match (uu___2_455) with
| String (b) -> begin
b
end
| Path (b) -> begin
(FStar_Common.try_convert_file_name_to_mixed b)
end
| uu____461 -> begin
(failwith "Impos: expected String")
end))


let as_list' : option_val  ->  option_val Prims.list = (fun uu___3_471 -> (match (uu___3_471) with
| List (ts) -> begin
ts
end
| uu____477 -> begin
(failwith "Impos: expected List")
end))


let as_list : 'Auu____488 . (option_val  ->  'Auu____488)  ->  option_val  ->  'Auu____488 Prims.list = (fun as_t x -> (

let uu____506 = (as_list' x)
in (FStar_All.pipe_right uu____506 (FStar_List.map as_t))))


let as_option : 'Auu____520 . (option_val  ->  'Auu____520)  ->  option_val  ->  'Auu____520 FStar_Pervasives_Native.option = (fun as_t uu___4_535 -> (match (uu___4_535) with
| Unset -> begin
FStar_Pervasives_Native.None
end
| v1 -> begin
(

let uu____539 = (as_t v1)
in FStar_Pervasives_Native.Some (uu____539))
end))


let as_comma_string_list : option_val  ->  Prims.string Prims.list = (fun uu___5_548 -> (match (uu___5_548) with
| List (ls) -> begin
(

let uu____555 = (FStar_List.map (fun l -> (

let uu____567 = (as_string l)
in (FStar_Util.split uu____567 ","))) ls)
in (FStar_All.pipe_left FStar_List.flatten uu____555))
end
| uu____579 -> begin
(failwith "Impos: expected String (comma list)")
end))


type optionstate =
option_val FStar_Util.smap


let copy_optionstate : 'Auu____591 . 'Auu____591 FStar_Util.smap  ->  'Auu____591 FStar_Util.smap = (fun m -> (FStar_Util.smap_copy m))


let fstar_options : optionstate Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let internal_peek : unit  ->  optionstate = (fun uu____621 -> (

let uu____622 = (

let uu____625 = (FStar_ST.op_Bang fstar_options)
in (FStar_List.hd uu____625))
in (FStar_List.hd uu____622)))


let peek : unit  ->  optionstate = (fun uu____664 -> (internal_peek ()))


let pop : unit  ->  unit = (fun uu____670 -> (

let uu____671 = (FStar_ST.op_Bang fstar_options)
in (match (uu____671) with
| [] -> begin
(failwith "TOO MANY POPS!")
end
| (uu____706)::[] -> begin
(failwith "TOO MANY POPS!")
end
| (uu____714)::tl1 -> begin
(FStar_ST.op_Colon_Equals fstar_options tl1)
end)))


let push : unit  ->  unit = (fun uu____756 -> (

let uu____757 = (

let uu____762 = (

let uu____765 = (

let uu____768 = (FStar_ST.op_Bang fstar_options)
in (FStar_List.hd uu____768))
in (FStar_List.map copy_optionstate uu____765))
in (

let uu____802 = (FStar_ST.op_Bang fstar_options)
in (uu____762)::uu____802))
in (FStar_ST.op_Colon_Equals fstar_options uu____757)))


let internal_pop : unit  ->  Prims.bool = (fun uu____869 -> (

let curstack = (

let uu____873 = (FStar_ST.op_Bang fstar_options)
in (FStar_List.hd uu____873))
in (match (curstack) with
| [] -> begin
(failwith "impossible: empty current option stack")
end
| (uu____910)::[] -> begin
false
end
| (uu____912)::tl1 -> begin
((

let uu____917 = (

let uu____922 = (

let uu____927 = (FStar_ST.op_Bang fstar_options)
in (FStar_List.tl uu____927))
in (tl1)::uu____922)
in (FStar_ST.op_Colon_Equals fstar_options uu____917));
true;
)
end)))


let internal_push : unit  ->  unit = (fun uu____996 -> (

let curstack = (

let uu____1000 = (FStar_ST.op_Bang fstar_options)
in (FStar_List.hd uu____1000))
in (

let stack' = (

let uu____1037 = (

let uu____1038 = (FStar_List.hd curstack)
in (copy_optionstate uu____1038))
in (uu____1037)::curstack)
in (

let uu____1041 = (

let uu____1046 = (

let uu____1051 = (FStar_ST.op_Bang fstar_options)
in (FStar_List.tl uu____1051))
in (stack')::uu____1046)
in (FStar_ST.op_Colon_Equals fstar_options uu____1041)))))


let set : optionstate  ->  unit = (fun o -> (

let uu____1120 = (FStar_ST.op_Bang fstar_options)
in (match (uu____1120) with
| [] -> begin
(failwith "set on empty option stack")
end
| ([])::uu____1155 -> begin
(failwith "set on empty current option stack")
end
| ((uu____1163)::tl1)::os -> begin
(FStar_ST.op_Colon_Equals fstar_options (((o)::tl1)::os))
end)))


let snapshot : unit  ->  (Prims.int * unit) = (fun uu____1213 -> (FStar_Common.snapshot push fstar_options ()))


let rollback : Prims.int FStar_Pervasives_Native.option  ->  unit = (fun depth -> (FStar_Common.rollback pop fstar_options depth))


let set_option : Prims.string  ->  option_val  ->  unit = (fun k v1 -> (

let uu____1243 = (peek ())
in (FStar_Util.smap_add uu____1243 k v1)))


let set_option' : (Prims.string * option_val)  ->  unit = (fun uu____1256 -> (match (uu____1256) with
| (k, v1) -> begin
(set_option k v1)
end))


let light_off_files : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let add_light_off_file : Prims.string  ->  unit = (fun filename -> (

let uu____1284 = (

let uu____1288 = (FStar_ST.op_Bang light_off_files)
in (filename)::uu____1288)
in (FStar_ST.op_Colon_Equals light_off_files uu____1284)))


let defaults : (Prims.string * option_val) Prims.list = ((("__temp_no_proj"), (List ([]))))::((("__temp_fast_implicits"), (Bool (false))))::((("abort_on"), (Int ((Prims.parse_int "0")))))::((("admit_smt_queries"), (Bool (false))))::((("admit_except"), (Unset)))::((("already_cached"), (Unset)))::((("cache_checked_modules"), (Bool (false))))::((("cache_dir"), (Unset)))::((("cache_off"), (Bool (false))))::((("cmi"), (Bool (false))))::((("codegen"), (Unset)))::((("codegen-lib"), (List ([]))))::((("debug"), (List ([]))))::((("debug_level"), (List ([]))))::((("defensive"), (String ("no"))))::((("dep"), (Unset)))::((("detail_errors"), (Bool (false))))::((("detail_hint_replay"), (Bool (false))))::((("doc"), (Bool (false))))::((("dump_module"), (List ([]))))::((("eager_subtyping"), (Bool (false))))::((("expose_interfaces"), (Bool (false))))::((("extract"), (Unset)))::((("extract_all"), (Bool (false))))::((("extract_module"), (List ([]))))::((("extract_namespace"), (List ([]))))::((("fs_typ_app"), (Bool (false))))::((("full_context_dependency"), (Bool (true))))::((("hide_uvar_nums"), (Bool (false))))::((("hint_info"), (Bool (false))))::((("hint_file"), (Unset)))::((("in"), (Bool (false))))::((("ide"), (Bool (false))))::((("include"), (List ([]))))::((("print"), (Bool (false))))::((("print_in_place"), (Bool (false))))::((("profile"), (Bool (false))))::((("initial_fuel"), (Int ((Prims.parse_int "2")))))::((("initial_ifuel"), (Int ((Prims.parse_int "1")))))::((("keep_query_captions"), (Bool (true))))::((("lax"), (Bool (false))))::((("load"), (List ([]))))::((("log_queries"), (Bool (false))))::((("log_types"), (Bool (false))))::((("max_fuel"), (Int ((Prims.parse_int "8")))))::((("max_ifuel"), (Int ((Prims.parse_int "2")))))::((("min_fuel"), (Int ((Prims.parse_int "1")))))::((("MLish"), (Bool (false))))::((("n_cores"), (Int ((Prims.parse_int "1")))))::((("no_default_includes"), (Bool (false))))::((("no_extract"), (List ([]))))::((("no_location_info"), (Bool (false))))::((("no_smt"), (Bool (false))))::((("no_plugins"), (Bool (false))))::((("no_tactics"), (Bool (false))))::((("normalize_pure_terms_for_extraction"), (Bool (false))))::((("odir"), (Unset)))::((("prims"), (Unset)))::((("pretype"), (Bool (true))))::((("prims_ref"), (Unset)))::((("print_bound_var_types"), (Bool (false))))::((("print_effect_args"), (Bool (false))))::((("print_full_names"), (Bool (false))))::((("print_implicits"), (Bool (false))))::((("print_universes"), (Bool (false))))::((("print_z3_statistics"), (Bool (false))))::((("prn"), (Bool (false))))::((("query_stats"), (Bool (false))))::((("record_hints"), (Bool (false))))::((("report_qi"), (Bool (false))))::((("reuse_hint_for"), (Unset)))::((("silent"), (Bool (false))))::((("smt"), (Unset)))::((("smtencoding.elim_box"), (Bool (false))))::((("smtencoding.nl_arith_repr"), (String ("boxwrap"))))::((("smtencoding.l_arith_repr"), (String ("boxwrap"))))::((("smtencoding.valid_intro"), (Bool (true))))::((("smtencoding.valid_elim"), (Bool (false))))::((("tactics_failhard"), (Bool (false))))::((("tactics_info"), (Bool (false))))::((("tactic_raw_binders"), (Bool (false))))::((("tactic_trace"), (Bool (false))))::((("tactic_trace_d"), (Int ((Prims.parse_int "0")))))::((("tcnorm"), (Bool (true))))::((("timing"), (Bool (false))))::((("trace_error"), (Bool (false))))::((("ugly"), (Bool (false))))::((("unthrottle_inductives"), (Bool (false))))::((("unsafe_tactic_exec"), (Bool (false))))::((("use_native_tactics"), (Unset)))::((("use_eq_at_higher_order"), (Bool (false))))::((("use_hints"), (Bool (false))))::((("use_hint_hashes"), (Bool (false))))::((("using_facts_from"), (Unset)))::((("vcgen.optimize_bind_as_seq"), (Unset)))::((("verify_module"), (List ([]))))::((("warn_default_effects"), (Bool (false))))::((("z3refresh"), (Bool (false))))::((("z3rlimit"), (Int ((Prims.parse_int "5")))))::((("z3rlimit_factor"), (Int ((Prims.parse_int "1")))))::((("z3seed"), (Int ((Prims.parse_int "0")))))::((("z3cliopt"), (List ([]))))::((("use_two_phase_tc"), (Bool (true))))::((("__no_positivity"), (Bool (false))))::((("__ml_no_eta_expand_coertions"), (Bool (false))))::((("__tactics_nbe"), (Bool (false))))::((("warn_error"), (List ([]))))::((("use_extracted_interfaces"), (Bool (false))))::((("use_nbe"), (Bool (false))))::[]


let parse_warn_error_set_get : (((Prims.string  ->  error_flag Prims.list)  ->  unit) * (unit  ->  Prims.string  ->  error_flag Prims.list)) = (

let r = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let set1 = (fun f -> (

let uu____2265 = (FStar_ST.op_Bang r)
in (match (uu____2265) with
| FStar_Pervasives_Native.None -> begin
(FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some (f)))
end
| uu____2356 -> begin
(failwith "Multiple initialization of FStar.Options")
end)))
in (

let get1 = (fun uu____2377 -> (

let uu____2378 = (FStar_ST.op_Bang r)
in (match (uu____2378) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(failwith "FStar.Options is improperly initialized")
end)))
in ((set1), (get1)))))


let initialize_parse_warn_error : (Prims.string  ->  error_flag Prims.list)  ->  unit = (fun f -> (FStar_Pervasives_Native.fst parse_warn_error_set_get f))


let parse_warn_error : Prims.string  ->  error_flag Prims.list = (fun s -> (

let uu____2517 = (FStar_Pervasives_Native.snd parse_warn_error_set_get ())
in (uu____2517 s)))


let init : unit  ->  unit = (fun uu____2548 -> (

let o = (peek ())
in ((FStar_Util.smap_clear o);
(FStar_All.pipe_right defaults (FStar_List.iter set_option'));
)))


let clear : unit  ->  unit = (fun uu____2568 -> (

let o = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_ST.op_Colon_Equals fstar_options (((o)::[])::[]));
(FStar_ST.op_Colon_Equals light_off_files []);
(init ());
)))


let _run : unit = (clear ())


let get_option : Prims.string  ->  option_val = (fun s -> (

let uu____2641 = (

let uu____2644 = (peek ())
in (FStar_Util.smap_try_find uu____2644 s))
in (match (uu____2641) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2647 = (

let uu____2649 = (FStar_String.op_Hat s " not found")
in (FStar_String.op_Hat "Impossible: option " uu____2649))
in (failwith uu____2647))
end
| FStar_Pervasives_Native.Some (s1) -> begin
s1
end)))


let lookup_opt : 'Auu____2661 . Prims.string  ->  (option_val  ->  'Auu____2661)  ->  'Auu____2661 = (fun s c -> (

let uu____2679 = (get_option s)
in (c uu____2679)))


let get_abort_on : unit  ->  Prims.int = (fun uu____2686 -> (lookup_opt "abort_on" as_int))


let get_admit_smt_queries : unit  ->  Prims.bool = (fun uu____2695 -> (lookup_opt "admit_smt_queries" as_bool))


let get_admit_except : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2706 -> (lookup_opt "admit_except" (as_option as_string)))


let get_already_cached : unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____2722 -> (lookup_opt "already_cached" (as_option (as_list as_string))))


let get_cache_checked_modules : unit  ->  Prims.bool = (fun uu____2739 -> (lookup_opt "cache_checked_modules" as_bool))


let get_cache_dir : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2750 -> (lookup_opt "cache_dir" (as_option as_string)))


let get_cache_off : unit  ->  Prims.bool = (fun uu____2762 -> (lookup_opt "cache_off" as_bool))


let get_cmi : unit  ->  Prims.bool = (fun uu____2771 -> (lookup_opt "cmi" as_bool))


let get_codegen : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2782 -> (lookup_opt "codegen" (as_option as_string)))


let get_codegen_lib : unit  ->  Prims.string Prims.list = (fun uu____2796 -> (lookup_opt "codegen-lib" (as_list as_string)))


let get_debug : unit  ->  Prims.string Prims.list = (fun uu____2810 -> (lookup_opt "debug" (as_list as_string)))


let get_debug_level : unit  ->  Prims.string Prims.list = (fun uu____2824 -> (lookup_opt "debug_level" as_comma_string_list))


let get_defensive : unit  ->  Prims.string = (fun uu____2835 -> (lookup_opt "defensive" as_string))


let get_dep : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2846 -> (lookup_opt "dep" (as_option as_string)))


let get_detail_errors : unit  ->  Prims.bool = (fun uu____2858 -> (lookup_opt "detail_errors" as_bool))


let get_detail_hint_replay : unit  ->  Prims.bool = (fun uu____2867 -> (lookup_opt "detail_hint_replay" as_bool))


let get_doc : unit  ->  Prims.bool = (fun uu____2876 -> (lookup_opt "doc" as_bool))


let get_dump_module : unit  ->  Prims.string Prims.list = (fun uu____2887 -> (lookup_opt "dump_module" (as_list as_string)))


let get_eager_subtyping : unit  ->  Prims.bool = (fun uu____2899 -> (lookup_opt "eager_subtyping" as_bool))


let get_expose_interfaces : unit  ->  Prims.bool = (fun uu____2908 -> (lookup_opt "expose_interfaces" as_bool))


let get_extract : unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____2921 -> (lookup_opt "extract" (as_option (as_list as_string))))


let get_extract_module : unit  ->  Prims.string Prims.list = (fun uu____2940 -> (lookup_opt "extract_module" (as_list as_string)))


let get_extract_namespace : unit  ->  Prims.string Prims.list = (fun uu____2954 -> (lookup_opt "extract_namespace" (as_list as_string)))


let get_fs_typ_app : unit  ->  Prims.bool = (fun uu____2966 -> (lookup_opt "fs_typ_app" as_bool))


let get_hide_uvar_nums : unit  ->  Prims.bool = (fun uu____2975 -> (lookup_opt "hide_uvar_nums" as_bool))


let get_hint_info : unit  ->  Prims.bool = (fun uu____2984 -> (lookup_opt "hint_info" as_bool))


let get_hint_file : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2995 -> (lookup_opt "hint_file" (as_option as_string)))


let get_in : unit  ->  Prims.bool = (fun uu____3007 -> (lookup_opt "in" as_bool))


let get_ide : unit  ->  Prims.bool = (fun uu____3016 -> (lookup_opt "ide" as_bool))


let get_include : unit  ->  Prims.string Prims.list = (fun uu____3027 -> (lookup_opt "include" (as_list as_string)))


let get_print : unit  ->  Prims.bool = (fun uu____3039 -> (lookup_opt "print" as_bool))


let get_print_in_place : unit  ->  Prims.bool = (fun uu____3048 -> (lookup_opt "print_in_place" as_bool))


let get_profile : unit  ->  Prims.bool = (fun uu____3057 -> (lookup_opt "profile" as_bool))


let get_initial_fuel : unit  ->  Prims.int = (fun uu____3066 -> (lookup_opt "initial_fuel" as_int))


let get_initial_ifuel : unit  ->  Prims.int = (fun uu____3075 -> (lookup_opt "initial_ifuel" as_int))


let get_keep_query_captions : unit  ->  Prims.bool = (fun uu____3084 -> (lookup_opt "keep_query_captions" as_bool))


let get_lax : unit  ->  Prims.bool = (fun uu____3093 -> (lookup_opt "lax" as_bool))


let get_load : unit  ->  Prims.string Prims.list = (fun uu____3104 -> (lookup_opt "load" (as_list as_string)))


let get_log_queries : unit  ->  Prims.bool = (fun uu____3116 -> (lookup_opt "log_queries" as_bool))


let get_log_types : unit  ->  Prims.bool = (fun uu____3125 -> (lookup_opt "log_types" as_bool))


let get_max_fuel : unit  ->  Prims.int = (fun uu____3134 -> (lookup_opt "max_fuel" as_int))


let get_max_ifuel : unit  ->  Prims.int = (fun uu____3143 -> (lookup_opt "max_ifuel" as_int))


let get_min_fuel : unit  ->  Prims.int = (fun uu____3152 -> (lookup_opt "min_fuel" as_int))


let get_MLish : unit  ->  Prims.bool = (fun uu____3161 -> (lookup_opt "MLish" as_bool))


let get_n_cores : unit  ->  Prims.int = (fun uu____3170 -> (lookup_opt "n_cores" as_int))


let get_no_default_includes : unit  ->  Prims.bool = (fun uu____3179 -> (lookup_opt "no_default_includes" as_bool))


let get_no_extract : unit  ->  Prims.string Prims.list = (fun uu____3190 -> (lookup_opt "no_extract" (as_list as_string)))


let get_no_location_info : unit  ->  Prims.bool = (fun uu____3202 -> (lookup_opt "no_location_info" as_bool))


let get_no_plugins : unit  ->  Prims.bool = (fun uu____3211 -> (lookup_opt "no_plugins" as_bool))


let get_no_smt : unit  ->  Prims.bool = (fun uu____3220 -> (lookup_opt "no_smt" as_bool))


let get_normalize_pure_terms_for_extraction : unit  ->  Prims.bool = (fun uu____3229 -> (lookup_opt "normalize_pure_terms_for_extraction" as_bool))


let get_odir : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3240 -> (lookup_opt "odir" (as_option as_string)))


let get_ugly : unit  ->  Prims.bool = (fun uu____3252 -> (lookup_opt "ugly" as_bool))


let get_prims : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3263 -> (lookup_opt "prims" (as_option as_string)))


let get_print_bound_var_types : unit  ->  Prims.bool = (fun uu____3275 -> (lookup_opt "print_bound_var_types" as_bool))


let get_print_effect_args : unit  ->  Prims.bool = (fun uu____3284 -> (lookup_opt "print_effect_args" as_bool))


let get_print_full_names : unit  ->  Prims.bool = (fun uu____3293 -> (lookup_opt "print_full_names" as_bool))


let get_print_implicits : unit  ->  Prims.bool = (fun uu____3302 -> (lookup_opt "print_implicits" as_bool))


let get_print_universes : unit  ->  Prims.bool = (fun uu____3311 -> (lookup_opt "print_universes" as_bool))


let get_print_z3_statistics : unit  ->  Prims.bool = (fun uu____3320 -> (lookup_opt "print_z3_statistics" as_bool))


let get_prn : unit  ->  Prims.bool = (fun uu____3329 -> (lookup_opt "prn" as_bool))


let get_query_stats : unit  ->  Prims.bool = (fun uu____3338 -> (lookup_opt "query_stats" as_bool))


let get_record_hints : unit  ->  Prims.bool = (fun uu____3347 -> (lookup_opt "record_hints" as_bool))


let get_report_qi : unit  ->  Prims.bool = (fun uu____3356 -> (lookup_opt "report_qi" as_bool))


let get_reuse_hint_for : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3367 -> (lookup_opt "reuse_hint_for" (as_option as_string)))


let get_silent : unit  ->  Prims.bool = (fun uu____3379 -> (lookup_opt "silent" as_bool))


let get_smt : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3390 -> (lookup_opt "smt" (as_option as_string)))


let get_smtencoding_elim_box : unit  ->  Prims.bool = (fun uu____3402 -> (lookup_opt "smtencoding.elim_box" as_bool))


let get_smtencoding_nl_arith_repr : unit  ->  Prims.string = (fun uu____3411 -> (lookup_opt "smtencoding.nl_arith_repr" as_string))


let get_smtencoding_l_arith_repr : unit  ->  Prims.string = (fun uu____3420 -> (lookup_opt "smtencoding.l_arith_repr" as_string))


let get_smtencoding_valid_intro : unit  ->  Prims.bool = (fun uu____3429 -> (lookup_opt "smtencoding.valid_intro" as_bool))


let get_smtencoding_valid_elim : unit  ->  Prims.bool = (fun uu____3438 -> (lookup_opt "smtencoding.valid_elim" as_bool))


let get_tactic_raw_binders : unit  ->  Prims.bool = (fun uu____3447 -> (lookup_opt "tactic_raw_binders" as_bool))


let get_tactics_failhard : unit  ->  Prims.bool = (fun uu____3456 -> (lookup_opt "tactics_failhard" as_bool))


let get_tactics_info : unit  ->  Prims.bool = (fun uu____3465 -> (lookup_opt "tactics_info" as_bool))


let get_tactic_trace : unit  ->  Prims.bool = (fun uu____3474 -> (lookup_opt "tactic_trace" as_bool))


let get_tactic_trace_d : unit  ->  Prims.int = (fun uu____3483 -> (lookup_opt "tactic_trace_d" as_int))


let get_tactics_nbe : unit  ->  Prims.bool = (fun uu____3492 -> (lookup_opt "__tactics_nbe" as_bool))


let get_tcnorm : unit  ->  Prims.bool = (fun uu____3501 -> (lookup_opt "tcnorm" as_bool))


let get_timing : unit  ->  Prims.bool = (fun uu____3510 -> (lookup_opt "timing" as_bool))


let get_trace_error : unit  ->  Prims.bool = (fun uu____3519 -> (lookup_opt "trace_error" as_bool))


let get_unthrottle_inductives : unit  ->  Prims.bool = (fun uu____3528 -> (lookup_opt "unthrottle_inductives" as_bool))


let get_unsafe_tactic_exec : unit  ->  Prims.bool = (fun uu____3537 -> (lookup_opt "unsafe_tactic_exec" as_bool))


let get_use_eq_at_higher_order : unit  ->  Prims.bool = (fun uu____3546 -> (lookup_opt "use_eq_at_higher_order" as_bool))


let get_use_hints : unit  ->  Prims.bool = (fun uu____3555 -> (lookup_opt "use_hints" as_bool))


let get_use_hint_hashes : unit  ->  Prims.bool = (fun uu____3564 -> (lookup_opt "use_hint_hashes" as_bool))


let get_use_native_tactics : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3575 -> (lookup_opt "use_native_tactics" (as_option as_string)))


let get_use_tactics : unit  ->  Prims.bool = (fun uu____3587 -> (

let uu____3588 = (lookup_opt "no_tactics" as_bool)
in (not (uu____3588))))


let get_using_facts_from : unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____3602 -> (lookup_opt "using_facts_from" (as_option (as_list as_string))))


let get_vcgen_optimize_bind_as_seq : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3621 -> (lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)))


let get_verify_module : unit  ->  Prims.string Prims.list = (fun uu____3635 -> (lookup_opt "verify_module" (as_list as_string)))


let get___temp_no_proj : unit  ->  Prims.string Prims.list = (fun uu____3649 -> (lookup_opt "__temp_no_proj" (as_list as_string)))


let get_version : unit  ->  Prims.bool = (fun uu____3661 -> (lookup_opt "version" as_bool))


let get_warn_default_effects : unit  ->  Prims.bool = (fun uu____3670 -> (lookup_opt "warn_default_effects" as_bool))


let get_z3cliopt : unit  ->  Prims.string Prims.list = (fun uu____3681 -> (lookup_opt "z3cliopt" (as_list as_string)))


let get_z3refresh : unit  ->  Prims.bool = (fun uu____3693 -> (lookup_opt "z3refresh" as_bool))


let get_z3rlimit : unit  ->  Prims.int = (fun uu____3702 -> (lookup_opt "z3rlimit" as_int))


let get_z3rlimit_factor : unit  ->  Prims.int = (fun uu____3711 -> (lookup_opt "z3rlimit_factor" as_int))


let get_z3seed : unit  ->  Prims.int = (fun uu____3720 -> (lookup_opt "z3seed" as_int))


let get_use_two_phase_tc : unit  ->  Prims.bool = (fun uu____3729 -> (lookup_opt "use_two_phase_tc" as_bool))


let get_no_positivity : unit  ->  Prims.bool = (fun uu____3738 -> (lookup_opt "__no_positivity" as_bool))


let get_ml_no_eta_expand_coertions : unit  ->  Prims.bool = (fun uu____3747 -> (lookup_opt "__ml_no_eta_expand_coertions" as_bool))


let get_warn_error : unit  ->  Prims.string Prims.list = (fun uu____3758 -> (lookup_opt "warn_error" (as_list as_string)))


let get_use_extracted_interfaces : unit  ->  Prims.bool = (fun uu____3770 -> (lookup_opt "use_extracted_interfaces" as_bool))


let get_use_nbe : unit  ->  Prims.bool = (fun uu____3779 -> (lookup_opt "use_nbe" as_bool))


let dlevel : Prims.string  ->  debug_level_t = (fun uu___6_3788 -> (match (uu___6_3788) with
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
| Other (uu____3809) -> begin
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

let uu____3818 = (get_debug_level ())
in (FStar_All.pipe_right uu____3818 (FStar_Util.for_some (fun l1 -> (one_debug_level_geq (dlevel l1) l2))))))


let universe_include_path_base_dirs : Prims.string Prims.list = ("/ulib")::("/lib/fstar")::[]


let _version : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _platform : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _compiler : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _date : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "<not set>")


let _commit : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let display_version : unit  ->  unit = (fun uu____3874 -> (

let uu____3875 = (

let uu____3877 = (FStar_ST.op_Bang _version)
in (

let uu____3900 = (FStar_ST.op_Bang _platform)
in (

let uu____3923 = (FStar_ST.op_Bang _compiler)
in (

let uu____3946 = (FStar_ST.op_Bang _date)
in (

let uu____3969 = (FStar_ST.op_Bang _commit)
in (FStar_Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____3877 uu____3900 uu____3923 uu____3946 uu____3969))))))
in (FStar_Util.print_string uu____3875)))


let display_usage_aux : 'Auu____4000 'Auu____4001 . ('Auu____4000 * Prims.string * 'Auu____4001 FStar_Getopt.opt_variant * Prims.string) Prims.list  ->  unit = (fun specs -> ((FStar_Util.print_string "fstar.exe [options] file[s]\n");
(FStar_List.iter (fun uu____4056 -> (match (uu____4056) with
| (uu____4069, flag, p, doc) -> begin
(match (p) with
| FStar_Getopt.ZeroArgs (ig) -> begin
(match ((Prims.op_Equality doc "")) with
| true -> begin
(

let uu____4088 = (

let uu____4090 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format1 "  --%s\n" uu____4090))
in (FStar_Util.print_string uu____4088))
end
| uu____4093 -> begin
(

let uu____4095 = (

let uu____4097 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format2 "  --%s  %s\n" uu____4097 doc))
in (FStar_Util.print_string uu____4095))
end)
end
| FStar_Getopt.OneArg (uu____4100, argname) -> begin
(match ((Prims.op_Equality doc "")) with
| true -> begin
(

let uu____4115 = (

let uu____4117 = (FStar_Util.colorize_bold flag)
in (

let uu____4119 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format2 "  --%s %s\n" uu____4117 uu____4119)))
in (FStar_Util.print_string uu____4115))
end
| uu____4122 -> begin
(

let uu____4124 = (

let uu____4126 = (FStar_Util.colorize_bold flag)
in (

let uu____4128 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format3 "  --%s %s  %s\n" uu____4126 uu____4128 doc)))
in (FStar_Util.print_string uu____4124))
end)
end)
end)) specs);
))


let mk_spec : (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant * Prims.string)  ->  FStar_Getopt.opt = (fun o -> (

let uu____4163 = o
in (match (uu____4163) with
| (ns, name, arg, desc) -> begin
(

let arg1 = (match (arg) with
| FStar_Getopt.ZeroArgs (f) -> begin
(

let g = (fun uu____4205 -> (

let uu____4206 = (f ())
in (set_option name uu____4206)))
in FStar_Getopt.ZeroArgs (g))
end
| FStar_Getopt.OneArg (f, d) -> begin
(

let g = (fun x -> (

let uu____4227 = (f x)
in (set_option name uu____4227)))
in FStar_Getopt.OneArg (((g), (d))))
end)
in ((ns), (name), (arg1), (desc)))
end)))


let accumulated_option : Prims.string  ->  option_val  ->  option_val = (fun name value -> (

let prev_values = (

let uu____4254 = (lookup_opt name (as_option as_list'))
in (FStar_Util.dflt [] uu____4254))
in List ((value)::prev_values)))


let reverse_accumulated_option : Prims.string  ->  option_val  ->  option_val = (fun name value -> (

let prev_values = (

let uu____4283 = (lookup_opt name (as_option as_list'))
in (FStar_Util.dflt [] uu____4283))
in List ((FStar_List.append prev_values ((value)::[])))))


let accumulate_string : 'Auu____4305 . Prims.string  ->  ('Auu____4305  ->  Prims.string)  ->  'Auu____4305  ->  unit = (fun name post_processor value -> (

let uu____4330 = (

let uu____4331 = (

let uu____4332 = (post_processor value)
in String (uu____4332))
in (accumulated_option name uu____4331))
in (set_option name uu____4330)))


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
| uu____4454 -> begin
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
| uu____4474 -> begin
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
| uu____4495 -> begin
false
end))


let uu___is_PathStr : opt_type  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PathStr (_0) -> begin
true
end
| uu____4508 -> begin
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
| uu____4531 -> begin
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
| uu____4556 -> begin
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
| uu____4592 -> begin
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
| uu____4642 -> begin
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
| uu____4682 -> begin
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
| uu____4701 -> begin
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
| uu____4727 -> begin
false
end))


let __proj__WithSideEffect__item___0 : opt_type  ->  ((unit  ->  unit) * opt_type) = (fun projectee -> (match (projectee) with
| WithSideEffect (_0) -> begin
_0
end))

exception InvalidArgument of (Prims.string)


let uu___is_InvalidArgument : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidArgument (uu____4770) -> begin
true
end
| uu____4773 -> begin
false
end))


let __proj__InvalidArgument__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidArgument (uu____4783) -> begin
uu____4783
end))


let rec parse_opt_val : Prims.string  ->  opt_type  ->  Prims.string  ->  option_val = (fun opt_name typ str_val -> (FStar_All.try_with (fun uu___295_4807 -> (match (()) with
| () -> begin
(match (typ) with
| Const (c) -> begin
c
end
| IntStr (uu____4809) -> begin
(

let uu____4811 = (FStar_Util.safe_int_of_string str_val)
in (match (uu____4811) with
| FStar_Pervasives_Native.Some (v1) -> begin
Int (v1)
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end))
end
| BoolStr -> begin
(

let uu____4819 = (match ((Prims.op_Equality str_val "true")) with
| true -> begin
true
end
| uu____4826 -> begin
(match ((Prims.op_Equality str_val "false")) with
| true -> begin
false
end
| uu____4833 -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end)
end)
in Bool (uu____4819))
end
| PathStr (uu____4836) -> begin
Path (str_val)
end
| SimpleStr (uu____4838) -> begin
String (str_val)
end
| EnumStr (strs) -> begin
(match ((FStar_List.mem str_val strs)) with
| true -> begin
String (str_val)
end
| uu____4846 -> begin
(FStar_Exn.raise (InvalidArgument (opt_name)))
end)
end
| OpenEnumStr (uu____4848) -> begin
String (str_val)
end
| PostProcessed (pp, elem_spec) -> begin
(

let uu____4865 = (parse_opt_val opt_name elem_spec str_val)
in (pp uu____4865))
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
end)) (fun uu___294_4882 -> (match (uu___294_4882) with
| InvalidArgument (opt_name1) -> begin
(

let uu____4885 = (FStar_Util.format1 "Invalid argument to --%s" opt_name1)
in (failwith uu____4885))
end))))


let rec desc_of_opt_type : opt_type  ->  Prims.string FStar_Pervasives_Native.option = (fun typ -> (

let desc_of_enum = (fun cases -> (

let uu____4915 = (

let uu____4917 = (FStar_String.op_Hat (FStar_String.concat "|" cases) "]")
in (FStar_String.op_Hat "[" uu____4917))
in FStar_Pervasives_Native.Some (uu____4915)))
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
| PostProcessed (uu____4959, elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| Accumulated (elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| ReverseAccumulated (elem_spec) -> begin
(desc_of_opt_type elem_spec)
end
| WithSideEffect (uu____4969, elem_spec) -> begin
(desc_of_opt_type elem_spec)
end)))


let rec arg_spec_of_opt_type : Prims.string  ->  opt_type  ->  option_val FStar_Getopt.opt_variant = (fun opt_name typ -> (

let parser = (parse_opt_val opt_name typ)
in (

let uu____5000 = (desc_of_opt_type typ)
in (match (uu____5000) with
| FStar_Pervasives_Native.None -> begin
FStar_Getopt.ZeroArgs ((fun uu____5008 -> (parser "")))
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

let uu____5034 = (

let uu____5036 = (as_string s)
in (FStar_String.lowercase uu____5036))
in String (uu____5034)))


let abort_counter : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let rec specs_with_types : unit  ->  (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list = (fun uu____5071 -> (((FStar_Getopt.noshort), ("abort_on"), (PostProcessed ((((fun uu___7_5106 -> (match (uu___7_5106) with
| Int (x) -> begin
((FStar_ST.op_Colon_Equals abort_counter x);
Int (x);
)
end
| x -> begin
(failwith "?")
end))), (IntStr ("non-negative integer"))))), ("Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")))::(((FStar_Getopt.noshort), ("admit_smt_queries"), (BoolStr), ("Admit SMT queries, unsafe! (default \'false\')")))::(((FStar_Getopt.noshort), ("admit_except"), (SimpleStr ("[symbol|(symbol, id)]")), ("Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except \'(FStar.Fin.pigeonhole, 1)\' or --admit_except FStar.Fin.pigeonhole)")))::(((FStar_Getopt.noshort), ("already_cached"), (Accumulated (SimpleStr ("One or more space-separated occurrences of \'[+|-]( * | namespace | module)\'"))), ("\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")))::(((FStar_Getopt.noshort), ("cache_checked_modules"), (Const (Bool (true))), ("Write a \'.checked\' file for each module after verification and read from it if present, instead of re-verifying")))::(((FStar_Getopt.noshort), ("cache_dir"), (PostProcessed (((pp_validate_dir), (PathStr ("dir"))))), ("Read and write .checked and .checked.lax in directory <dir>")))::(((FStar_Getopt.noshort), ("cache_off"), (Const (Bool (true))), ("Do not read or write any .checked files")))::(((FStar_Getopt.noshort), ("cmi"), (Const (Bool (true))), ("Inline across module interfaces during extraction (aka. cross-module inlining)")))::(((FStar_Getopt.noshort), ("codegen"), (EnumStr (("OCaml")::("FSharp")::("Kremlin")::("Plugin")::[])), ("Generate code for further compilation to executable code, or build a compiler plugin")))::(((FStar_Getopt.noshort), ("codegen-lib"), (Accumulated (SimpleStr ("namespace"))), ("External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")))::(((FStar_Getopt.noshort), ("debug"), (Accumulated (SimpleStr ("module_name"))), ("Print lots of debugging information while checking module")))::(((FStar_Getopt.noshort), ("debug_level"), (Accumulated (OpenEnumStr (((("Low")::("Medium")::("High")::("Extreme")::[]), ("..."))))), ("Control the verbosity of debugging info")))::(((FStar_Getopt.noshort), ("defensive"), (EnumStr (("no")::("warn")::("fail")::[])), ("Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif \'no\', no checks are performed\n\t\tif \'warn\', checks are performed and raise a warning when they fail\n\t\tif \'fail\', like \'warn\', but the compiler aborts instead of issuing a warning\n\t\t(default \'no\')")))::(((FStar_Getopt.noshort), ("dep"), (EnumStr (("make")::("graph")::("full")::("raw")::[])), ("Output the transitive closure of the full dependency graph in three formats:\n\t \'graph\': a format suitable the \'dot\' tool from \'GraphViz\'\n\t \'full\': a format suitable for \'make\', including dependences for producing .ml and .krml files\n\t \'make\': (deprecated) a format suitable for \'make\', including only dependences among source files")))::(((FStar_Getopt.noshort), ("detail_errors"), (Const (Bool (true))), ("Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")))::(((FStar_Getopt.noshort), ("detail_hint_replay"), (Const (Bool (true))), ("Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")))::(((FStar_Getopt.noshort), ("doc"), (Const (Bool (true))), ("Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")))::(((FStar_Getopt.noshort), ("dump_module"), (Accumulated (SimpleStr ("module_name"))), ("")))::(((FStar_Getopt.noshort), ("eager_subtyping"), (Const (Bool (true))), ("Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")))::(((FStar_Getopt.noshort), ("extract"), (Accumulated (SimpleStr ("One or more space-separated occurrences of \'[+|-]( * | namespace | module)\'"))), ("\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract \'* -FStar.Reflection +FStar.List -FStar.List.Tot\' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the \'+\' is optional: --extract \'+A\' and --extract \'A\' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract \'A B\'.")))::(((FStar_Getopt.noshort), ("extract_module"), (Accumulated (PostProcessed (((pp_lowercase), (SimpleStr ("module_name")))))), ("Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")))::(((FStar_Getopt.noshort), ("extract_namespace"), (Accumulated (PostProcessed (((pp_lowercase), (SimpleStr ("namespace name")))))), ("Deprecated: use --extract instead; Only extract modules in the specified namespace")))::(((FStar_Getopt.noshort), ("expose_interfaces"), (Const (Bool (true))), ("Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")))::(((FStar_Getopt.noshort), ("hide_uvar_nums"), (Const (Bool (true))), ("Don\'t print unification variable numbers")))::(((FStar_Getopt.noshort), ("hint_file"), (PathStr ("path")), ("Read/write hints to <path> (instead of module-specific hints files)")))::(((FStar_Getopt.noshort), ("hint_info"), (Const (Bool (true))), ("Print information regarding hints (deprecated; use --query_stats instead)")))::(((FStar_Getopt.noshort), ("in"), (Const (Bool (true))), ("Legacy interactive mode; reads input from stdin")))::(((FStar_Getopt.noshort), ("ide"), (Const (Bool (true))), ("JSON-based interactive mode for IDEs")))::(((FStar_Getopt.noshort), ("include"), (ReverseAccumulated (PathStr ("path"))), ("A directory in which to search for files included on the command line")))::(((FStar_Getopt.noshort), ("print"), (Const (Bool (true))), ("Parses and prettyprints the files included on the command line")))::(((FStar_Getopt.noshort), ("print_in_place"), (Const (Bool (true))), ("Parses and prettyprints in place the files included on the command line")))::(((FStar_Getopt.noshort), ("profile"), (Const (Bool (true))), ("Prints timing information for various operations in the compiler")))::(((FStar_Getopt.noshort), ("initial_fuel"), (IntStr ("non-negative integer")), ("Number of unrolling of recursive functions to try initially (default 2)")))::(((FStar_Getopt.noshort), ("initial_ifuel"), (IntStr ("non-negative integer")), ("Number of unrolling of inductive datatypes to try at first (default 1)")))::(((FStar_Getopt.noshort), ("keep_query_captions"), (BoolStr), ("Retain comments in the logged SMT queries (requires --log_queries; default true)")))::(((FStar_Getopt.noshort), ("lax"), (Const (Bool (true))), ("Run the lax-type checker only (admit all verification conditions)")))::(((FStar_Getopt.noshort), ("load"), (ReverseAccumulated (PathStr ("module"))), ("Load compiled module")))::(((FStar_Getopt.noshort), ("log_types"), (Const (Bool (true))), ("Print types computed for data/val/let-bindings")))::(((FStar_Getopt.noshort), ("log_queries"), (Const (Bool (true))), ("Log the Z3 queries in several queries-*.smt2 files, as we go")))::(((FStar_Getopt.noshort), ("max_fuel"), (IntStr ("non-negative integer")), ("Number of unrolling of recursive functions to try at most (default 8)")))::(((FStar_Getopt.noshort), ("max_ifuel"), (IntStr ("non-negative integer")), ("Number of unrolling of inductive datatypes to try at most (default 2)")))::(((FStar_Getopt.noshort), ("min_fuel"), (IntStr ("non-negative integer")), ("Minimum number of unrolling of recursive functions to try (default 1)")))::(((FStar_Getopt.noshort), ("MLish"), (Const (Bool (true))), ("Trigger various specializations for compiling the F* compiler itself (not meant for user code)")))::(((FStar_Getopt.noshort), ("n_cores"), (IntStr ("positive_integer")), ("Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")))::(((FStar_Getopt.noshort), ("no_default_includes"), (Const (Bool (true))), ("Ignore the default module search paths")))::(((FStar_Getopt.noshort), ("no_extract"), (Accumulated (PathStr ("module name"))), ("Deprecated: use --extract instead; Do not extract code from this module")))::(((FStar_Getopt.noshort), ("no_location_info"), (Const (Bool (true))), ("Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")))::(((FStar_Getopt.noshort), ("no_smt"), (Const (Bool (true))), ("Do not send any queries to the SMT solver, and fail on them instead")))::(((FStar_Getopt.noshort), ("normalize_pure_terms_for_extraction"), (Const (Bool (true))), ("Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")))::(((FStar_Getopt.noshort), ("odir"), (PostProcessed (((pp_validate_dir), (PathStr ("dir"))))), ("Place output in directory <dir>")))::(((FStar_Getopt.noshort), ("prims"), (PathStr ("file")), ("")))::(((FStar_Getopt.noshort), ("print_bound_var_types"), (Const (Bool (true))), ("Print the types of bound variables")))::(((FStar_Getopt.noshort), ("print_effect_args"), (Const (Bool (true))), ("Print inferred predicate transformers for all computation types")))::(((FStar_Getopt.noshort), ("print_full_names"), (Const (Bool (true))), ("Print full names of variables")))::(((FStar_Getopt.noshort), ("print_implicits"), (Const (Bool (true))), ("Print implicit arguments")))::(((FStar_Getopt.noshort), ("print_universes"), (Const (Bool (true))), ("Print universes")))::(((FStar_Getopt.noshort), ("print_z3_statistics"), (Const (Bool (true))), ("Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)")))::(((FStar_Getopt.noshort), ("prn"), (Const (Bool (true))), ("Print full names (deprecated; use --print_full_names instead)")))::(((FStar_Getopt.noshort), ("query_stats"), (Const (Bool (true))), ("Print SMT query statistics")))::(((FStar_Getopt.noshort), ("record_hints"), (Const (Bool (true))), ("Record a database of hints for efficient proof replay")))::(((FStar_Getopt.noshort), ("report_qi"), (Const (Bool (true))), ("Generates a quantifier instantiation report every time Z3 is closed")))::(((FStar_Getopt.noshort), ("reuse_hint_for"), (SimpleStr ("toplevel_name")), ("Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term \'g\'")))::(((FStar_Getopt.noshort), ("silent"), (Const (Bool (true))), ("Disable all non-critical output")))::(((FStar_Getopt.noshort), ("smt"), (PathStr ("path")), ("Path to the Z3 SMT solver (we could eventually support other solvers)")))::(((FStar_Getopt.noshort), ("smtencoding.elim_box"), (BoolStr), ("Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default \'false\')")))::(((FStar_Getopt.noshort), ("smtencoding.nl_arith_repr"), (EnumStr (("native")::("wrapped")::("boxwrap")::[])), ("Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if \'boxwrap\' use \'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus\'; \n\t\tif \'native\' use \'*, div, mod\';\n\t\tif \'wrapped\' use \'_mul, _div, _mod : Int*Int -> Int\'; \n\t\t(default \'boxwrap\')")))::(((FStar_Getopt.noshort), ("smtencoding.l_arith_repr"), (EnumStr (("native")::("boxwrap")::[])), ("Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if \'boxwrap\', use \'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus\'; \n\t\tif \'native\', use \'+, -, -\'; \n\t\t(default \'boxwrap\')")))::(((FStar_Getopt.noshort), ("smtencoding.valid_intro"), (BoolStr), ("Include an axiom in the SMT encoding to introduce proof-irrelevance from a constructive proof")))::(((FStar_Getopt.noshort), ("smtencoding.valid_elim"), (BoolStr), ("Include an axiom in the SMT encoding to eliminate proof-irrelevance into the existence of a proof witness")))::(((FStar_Getopt.noshort), ("tactic_raw_binders"), (Const (Bool (true))), ("Do not use the lexical scope of tactics to improve binder names")))::(((FStar_Getopt.noshort), ("tactics_failhard"), (Const (Bool (true))), ("Do not recover from metaprogramming errors, and abort if one occurs")))::(((FStar_Getopt.noshort), ("tactics_info"), (Const (Bool (true))), ("Print some rough information on tactics, such as the time they take to run")))::(((FStar_Getopt.noshort), ("tactic_trace"), (Const (Bool (true))), ("Print a depth-indexed trace of tactic execution (Warning: very verbose)")))::(((FStar_Getopt.noshort), ("tactic_trace_d"), (IntStr ("positive_integer")), ("Trace tactics up to a certain binding depth")))::(((FStar_Getopt.noshort), ("__tactics_nbe"), (Const (Bool (true))), ("Use NBE to evaluate metaprograms (experimental)")))::(((FStar_Getopt.noshort), ("tcnorm"), (BoolStr), ("Attempt to normalize definitions marked as tcnorm (default \'true\')")))::(((FStar_Getopt.noshort), ("timing"), (Const (Bool (true))), ("Print the time it takes to verify each top-level definition")))::(((FStar_Getopt.noshort), ("trace_error"), (Const (Bool (true))), ("Don\'t print an error message; show an exception trace instead")))::(((FStar_Getopt.noshort), ("ugly"), (Const (Bool (true))), ("Emit output formatted for debugging")))::(((FStar_Getopt.noshort), ("unthrottle_inductives"), (Const (Bool (true))), ("Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")))::(((FStar_Getopt.noshort), ("unsafe_tactic_exec"), (Const (Bool (true))), ("Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")))::(((FStar_Getopt.noshort), ("use_eq_at_higher_order"), (Const (Bool (true))), ("Use equality constraints when comparing higher-order types (Temporary)")))::(((FStar_Getopt.noshort), ("use_hints"), (Const (Bool (true))), ("Use a previously recorded hints database for proof replay")))::(((FStar_Getopt.noshort), ("use_hint_hashes"), (Const (Bool (true))), ("Admit queries if their hash matches the hash recorded in the hints database")))::(((FStar_Getopt.noshort), ("use_native_tactics"), (PathStr ("path")), ("Use compiled tactics from <path>")))::(((FStar_Getopt.noshort), ("no_plugins"), (Const (Bool (true))), ("Do not run plugins natively and interpret them as usual instead")))::(((FStar_Getopt.noshort), ("no_tactics"), (Const (Bool (true))), ("Do not run the tactic engine before discharging a VC")))::(((FStar_Getopt.noshort), ("using_facts_from"), (ReverseAccumulated (SimpleStr ("One or more space-separated occurrences of \'[+|-]( * | namespace | fact id)\'"))), ("\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from \'* -FStar.Reflection +FStar.List -FStar.List.Tot\' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the \'+\' is optional: --using_facts_from \'FStar.List\' is equivalent to --using_facts_from \'+FStar.List\'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")))::(((FStar_Getopt.noshort), ("vcgen.optimize_bind_as_seq"), (EnumStr (("off")::("without_type")::("with_type")::[])), ("\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")))::(((FStar_Getopt.noshort), ("__temp_no_proj"), (Accumulated (SimpleStr ("module_name"))), ("Don\'t generate projectors for this module")))::(((FStar_Getopt.noshort), ("__temp_fast_implicits"), (Const (Bool (true))), ("Don\'t use this option yet")))::(((118 (*v*)), ("version"), (WithSideEffect ((((fun uu____6743 -> ((display_version ());
(FStar_All.exit (Prims.parse_int "0"));
))), (Const (Bool (true)))))), ("Display version number")))::(((FStar_Getopt.noshort), ("warn_default_effects"), (Const (Bool (true))), ("Warn when (a -> b) is desugared to (a -> Tot b)")))::(((FStar_Getopt.noshort), ("z3cliopt"), (ReverseAccumulated (SimpleStr ("option"))), ("Z3 command line options")))::(((FStar_Getopt.noshort), ("z3refresh"), (Const (Bool (true))), ("Restart Z3 after each query; useful for ensuring proof robustness")))::(((FStar_Getopt.noshort), ("z3rlimit"), (IntStr ("positive_integer")), ("Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")))::(((FStar_Getopt.noshort), ("z3rlimit_factor"), (IntStr ("positive_integer")), ("Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")))::(((FStar_Getopt.noshort), ("z3seed"), (IntStr ("positive_integer")), ("Set the Z3 random seed (default 0)")))::(((FStar_Getopt.noshort), ("use_two_phase_tc"), (BoolStr), ("Use the two phase typechecker (default \'true\')")))::(((FStar_Getopt.noshort), ("__no_positivity"), (Const (Bool (true))), ("Don\'t check positivity of inductive types")))::(((FStar_Getopt.noshort), ("__ml_no_eta_expand_coertions"), (Const (Bool (true))), ("Do not eta-expand coertions in generated OCaml")))::(((FStar_Getopt.noshort), ("warn_error"), (Accumulated (SimpleStr (""))), ("The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")))::(((FStar_Getopt.noshort), ("use_extracted_interfaces"), (BoolStr), ("Extract interfaces from the dependencies and use them for verification (default \'false\')")))::(((FStar_Getopt.noshort), ("use_nbe"), (BoolStr), ("Use normalization by evaluation as the default normalization srategy (default \'false\')")))::(((FStar_Getopt.noshort), ("__debug_embedding"), (WithSideEffect ((((fun uu____6968 -> (FStar_ST.op_Colon_Equals debug_embedding true))), (Const (Bool (true)))))), ("Debug messages for embeddings/unembeddings of natively compiled terms")))::(((FStar_Getopt.noshort), ("eager_embedding"), (WithSideEffect ((((fun uu____7012 -> (FStar_ST.op_Colon_Equals eager_embedding true))), (Const (Bool (true)))))), ("Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")))::(((104 (*h*)), ("help"), (WithSideEffect ((((fun uu____7058 -> ((

let uu____7060 = (specs ())
in (display_usage_aux uu____7060));
(FStar_All.exit (Prims.parse_int "0"));
))), (Const (Bool (true)))))), ("Display this information")))::[])
and specs : unit  ->  FStar_Getopt.opt Prims.list = (fun uu____7091 -> (

let uu____7094 = (specs_with_types ())
in (FStar_List.map (fun uu____7125 -> (match (uu____7125) with
| (short, long, typ, doc) -> begin
(

let uu____7147 = (

let uu____7161 = (arg_spec_of_opt_type long typ)
in ((short), (long), (uu____7161), (doc)))
in (mk_spec uu____7147))
end)) uu____7094)))


let settable : Prims.string  ->  Prims.bool = (fun uu___8_7176 -> (match (uu___8_7176) with
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
| "no_plugins" -> begin
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
| "tactics_failhard" -> begin
true
end
| "tactics_info" -> begin
true
end
| "tactic_trace" -> begin
true
end
| "tactic_trace_d" -> begin
true
end
| "tcnorm" -> begin
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
| uu____7297 -> begin
false
end))


let resettable : Prims.string  ->  Prims.bool = (fun s -> ((((((settable s) || (Prims.op_Equality s "z3seed")) || (Prims.op_Equality s "z3cliopt")) || (Prims.op_Equality s "using_facts_from")) || (Prims.op_Equality s "smtencoding.valid_intro")) || (Prims.op_Equality s "smtencoding.valid_elim")))


let all_specs : FStar_Getopt.opt Prims.list = (specs ())


let all_specs_with_types : (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list = (specs_with_types ())


let settable_specs : (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____7400 -> (match (uu____7400) with
| (uu____7415, x, uu____7417, uu____7418) -> begin
(settable x)
end))))


let resettable_specs : (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____7493 -> (match (uu____7493) with
| (uu____7508, x, uu____7510, uu____7511) -> begin
(resettable x)
end))))


let display_usage : unit  ->  unit = (fun uu____7527 -> (

let uu____7528 = (specs ())
in (display_usage_aux uu____7528)))


let fstar_bin_directory : Prims.string = (FStar_Util.get_exec_dir ())

exception File_argument of (Prims.string)


let uu___is_File_argument : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| File_argument (uu____7560) -> begin
true
end
| uu____7563 -> begin
false
end))


let __proj__File_argument__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| File_argument (uu____7573) -> begin
uu____7573
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
in (FStar_All.try_with (fun uu___472_7594 -> (match (()) with
| () -> begin
(match ((Prims.op_Equality s "")) with
| true -> begin
FStar_Getopt.Success
end
| uu____7598 -> begin
(FStar_Getopt.parse_string specs1 (fun s1 -> (FStar_Exn.raise (File_argument (s1)))) s)
end)
end)) (fun uu___471_7608 -> (match (uu___471_7608) with
| File_argument (s1) -> begin
(

let uu____7611 = (FStar_Util.format1 "File %s is not a valid option" s1)
in FStar_Getopt.Error (uu____7611))
end)))))


let file_list_ : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let parse_cmd_line : unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____7636 -> (

let res = (FStar_Getopt.parse_cmdline all_specs (fun i -> (

let uu____7642 = (

let uu____7646 = (FStar_ST.op_Bang file_list_)
in (FStar_List.append uu____7646 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list_ uu____7642))))
in (

let uu____7703 = (

let uu____7707 = (FStar_ST.op_Bang file_list_)
in (FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____7707))
in ((res), (uu____7703)))))


let file_list : unit  ->  Prims.string Prims.list = (fun uu____7749 -> (FStar_ST.op_Bang file_list_))


let restore_cmd_line_options : Prims.bool  ->  FStar_Getopt.parse_cmdline_res = (fun should_clear -> (

let old_verify_module = (get_verify_module ())
in ((match (should_clear) with
| true -> begin
(clear ())
end
| uu____7789 -> begin
(init ())
end);
(

let r = (

let uu____7792 = (specs ())
in (FStar_Getopt.parse_cmdline uu____7792 (fun x -> ())))
in ((

let uu____7799 = (

let uu____7805 = (

let uu____7806 = (FStar_List.map (fun _7810 -> String (_7810)) old_verify_module)
in List (uu____7806))
in (("verify_module"), (uu____7805)))
in (set_option' uu____7799));
r;
));
)))


let module_name_of_file_name : Prims.string  ->  Prims.string = (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let f2 = (

let uu____7826 = (

let uu____7828 = (

let uu____7830 = (

let uu____7832 = (FStar_Util.get_file_extension f1)
in (FStar_String.length uu____7832))
in ((FStar_String.length f1) - uu____7830))
in (uu____7828 - (Prims.parse_int "1")))
in (FStar_String.substring f1 (Prims.parse_int "0") uu____7826))
in (FStar_String.lowercase f2))))


let should_verify : Prims.string  ->  Prims.bool = (fun m -> (

let uu____7845 = (get_lax ())
in (match (uu____7845) with
| true -> begin
false
end
| uu____7850 -> begin
(

let l = (get_verify_module ())
in (FStar_List.contains (FStar_String.lowercase m) l))
end)))


let should_verify_file : Prims.string  ->  Prims.bool = (fun fn -> (

let uu____7866 = (module_name_of_file_name fn)
in (should_verify uu____7866)))


let module_name_eq : Prims.string  ->  Prims.string  ->  Prims.bool = (fun m1 m2 -> (Prims.op_Equality (FStar_String.lowercase m1) (FStar_String.lowercase m2)))


let dont_gen_projectors : Prims.string  ->  Prims.bool = (fun m -> (

let uu____7894 = (get___temp_no_proj ())
in (FStar_All.pipe_right uu____7894 (FStar_List.existsb (module_name_eq m)))))


let should_print_message : Prims.string  ->  Prims.bool = (fun m -> (

let uu____7912 = (should_verify m)
in (match (uu____7912) with
| true -> begin
(Prims.op_disEquality m "Prims")
end
| uu____7918 -> begin
false
end)))


let include_path : unit  ->  Prims.string Prims.list = (fun uu____7929 -> (

let cache_dir = (

let uu____7934 = (get_cache_dir ())
in (match (uu____7934) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (c) -> begin
(c)::[]
end))
in (

let uu____7948 = (get_no_default_includes ())
in (match (uu____7948) with
| true -> begin
(

let uu____7954 = (get_include ())
in (FStar_List.append cache_dir uu____7954))
end
| uu____7959 -> begin
(

let lib_paths = (

let uu____7965 = (FStar_Util.expand_environment_variable "FSTAR_LIB")
in (match (uu____7965) with
| FStar_Pervasives_Native.None -> begin
(

let fstar_home = (FStar_String.op_Hat fstar_bin_directory "/..")
in (

let defs = universe_include_path_base_dirs
in (

let uu____7981 = (FStar_All.pipe_right defs (FStar_List.map (fun x -> (FStar_String.op_Hat fstar_home x))))
in (FStar_All.pipe_right uu____7981 (FStar_List.filter FStar_Util.file_exists)))))
end
| FStar_Pervasives_Native.Some (s) -> begin
(s)::[]
end))
in (

let uu____8008 = (

let uu____8012 = (

let uu____8016 = (get_include ())
in (FStar_List.append uu____8016 ((".")::[])))
in (FStar_List.append lib_paths uu____8012))
in (FStar_List.append cache_dir uu____8008)))
end))))


let find_file : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (

let file_map = (FStar_Util.smap_create (Prims.parse_int "100"))
in (fun filename -> (

let uu____8047 = (FStar_Util.smap_try_find file_map filename)
in (match (uu____8047) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let result = (FStar_All.try_with (fun uu___523_8078 -> (match (()) with
| () -> begin
(

let uu____8082 = (FStar_Util.is_path_absolute filename)
in (match (uu____8082) with
| true -> begin
(match ((FStar_Util.file_exists filename)) with
| true -> begin
FStar_Pervasives_Native.Some (filename)
end
| uu____8093 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____8096 -> begin
(

let uu____8098 = (

let uu____8102 = (include_path ())
in (FStar_List.rev uu____8102))
in (FStar_Util.find_map uu____8098 (fun p -> (

let path = (match ((Prims.op_Equality p ".")) with
| true -> begin
filename
end
| uu____8119 -> begin
(FStar_Util.join_paths p filename)
end)
in (match ((FStar_Util.file_exists path)) with
| true -> begin
FStar_Pervasives_Native.Some (path)
end
| uu____8126 -> begin
FStar_Pervasives_Native.None
end)))))
end))
end)) (fun uu___522_8130 -> FStar_Pervasives_Native.None))
in ((match ((FStar_Option.isSome result)) with
| true -> begin
(FStar_Util.smap_add file_map filename result)
end
| uu____8141 -> begin
()
end);
result;
))
end))))


let prims : unit  ->  Prims.string = (fun uu____8149 -> (

let uu____8150 = (get_prims ())
in (match (uu____8150) with
| FStar_Pervasives_Native.None -> begin
(

let filename = "prims.fst"
in (

let uu____8159 = (find_file filename)
in (match (uu____8159) with
| FStar_Pervasives_Native.Some (result) -> begin
result
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8168 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____8168))
end)))
end
| FStar_Pervasives_Native.Some (x) -> begin
x
end)))


let prims_basename : unit  ->  Prims.string = (fun uu____8181 -> (

let uu____8182 = (prims ())
in (FStar_Util.basename uu____8182)))


let pervasives : unit  ->  Prims.string = (fun uu____8190 -> (

let filename = "FStar.Pervasives.fst"
in (

let uu____8194 = (find_file filename)
in (match (uu____8194) with
| FStar_Pervasives_Native.Some (result) -> begin
result
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8203 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____8203))
end))))


let pervasives_basename : unit  ->  Prims.string = (fun uu____8213 -> (

let uu____8214 = (pervasives ())
in (FStar_Util.basename uu____8214)))


let pervasives_native_basename : unit  ->  Prims.string = (fun uu____8222 -> (

let filename = "FStar.Pervasives.Native.fst"
in (

let uu____8226 = (find_file filename)
in (match (uu____8226) with
| FStar_Pervasives_Native.Some (result) -> begin
(FStar_Util.basename result)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8235 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in (failwith uu____8235))
end))))


let prepend_output_dir : Prims.string  ->  Prims.string = (fun fname -> (

let uu____8248 = (get_odir ())
in (match (uu____8248) with
| FStar_Pervasives_Native.None -> begin
fname
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Util.join_paths x fname)
end)))


let prepend_cache_dir : Prims.string  ->  Prims.string = (fun fpath -> (

let uu____8266 = (get_cache_dir ())
in (match (uu____8266) with
| FStar_Pervasives_Native.None -> begin
fpath
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____8275 = (FStar_Util.basename fpath)
in (FStar_Util.join_paths x uu____8275))
end)))


let path_of_text : Prims.string  ->  Prims.string Prims.list = (fun text -> (FStar_String.split ((46 (*.*))::[]) text))


let parse_settings : Prims.string Prims.list  ->  (Prims.string Prims.list * Prims.bool) Prims.list = (fun ns -> (

let cache = (FStar_Util.smap_create (Prims.parse_int "31"))
in (

let with_cache = (fun f s -> (

let uu____8397 = (FStar_Util.smap_try_find cache s)
in (match (uu____8397) with
| FStar_Pervasives_Native.Some (s1) -> begin
s1
end
| FStar_Pervasives_Native.None -> begin
(

let res = (f s)
in ((FStar_Util.smap_add cache s res);
res;
))
end)))
in (

let parse_one_setting = (fun s -> (match ((Prims.op_Equality s "*")) with
| true -> begin
(([]), (true))
end
| uu____8516 -> begin
(match ((Prims.op_Equality s "-*")) with
| true -> begin
(([]), (false))
end
| uu____8535 -> begin
(match ((FStar_Util.starts_with s "-")) with
| true -> begin
(

let path = (

let uu____8551 = (FStar_Util.substring_from s (Prims.parse_int "1"))
in (path_of_text uu____8551))
in ((path), (false)))
end
| uu____8559 -> begin
(

let s1 = (match ((FStar_Util.starts_with s "+")) with
| true -> begin
(FStar_Util.substring_from s (Prims.parse_int "1"))
end
| uu____8567 -> begin
s
end)
in (((path_of_text s1)), (true)))
end)
end)
end))
in (

let uu____8574 = (FStar_All.pipe_right ns (FStar_List.collect (fun s -> (

let s1 = (FStar_Util.trim_string s)
in (match ((Prims.op_Equality s1 "")) with
| true -> begin
[]
end
| uu____8634 -> begin
(with_cache (fun s2 -> (

let uu____8642 = (

let uu____8646 = (FStar_All.pipe_right (FStar_Util.splitlines s2) (FStar_List.concatMap (fun s3 -> (FStar_Util.split s3 " "))))
in (FStar_All.pipe_right uu____8646 (FStar_List.filter (fun s3 -> (Prims.op_disEquality s3 "")))))
in (FStar_All.pipe_right uu____8642 (FStar_List.map parse_one_setting)))) s1)
end)))))
in (FStar_All.pipe_right uu____8574 FStar_List.rev))))))


let __temp_no_proj : Prims.string  ->  Prims.bool = (fun s -> (

let uu____8733 = (get___temp_no_proj ())
in (FStar_All.pipe_right uu____8733 (FStar_List.contains s))))


let __temp_fast_implicits : unit  ->  Prims.bool = (fun uu____8748 -> (lookup_opt "__temp_fast_implicits" as_bool))


let admit_smt_queries : unit  ->  Prims.bool = (fun uu____8757 -> (get_admit_smt_queries ()))


let admit_except : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____8766 -> (get_admit_except ()))


let cache_checked_modules : unit  ->  Prims.bool = (fun uu____8773 -> (get_cache_checked_modules ()))


let cache_off : unit  ->  Prims.bool = (fun uu____8780 -> (get_cache_off ()))


let cmi : unit  ->  Prims.bool = (fun uu____8787 -> (get_cmi ()))

type codegen_t =
| OCaml
| FSharp
| Kremlin
| Plugin


let uu___is_OCaml : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OCaml -> begin
true
end
| uu____8797 -> begin
false
end))


let uu___is_FSharp : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FSharp -> begin
true
end
| uu____8808 -> begin
false
end))


let uu___is_Kremlin : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Kremlin -> begin
true
end
| uu____8819 -> begin
false
end))


let uu___is_Plugin : codegen_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Plugin -> begin
true
end
| uu____8830 -> begin
false
end))


let codegen : unit  ->  codegen_t FStar_Pervasives_Native.option = (fun uu____8839 -> (

let uu____8840 = (get_codegen ())
in (FStar_Util.map_opt uu____8840 (fun uu___9_8846 -> (match (uu___9_8846) with
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
| uu____8852 -> begin
(failwith "Impossible")
end)))))


let codegen_libs : unit  ->  Prims.string Prims.list Prims.list = (fun uu____8865 -> (

let uu____8866 = (get_codegen_lib ())
in (FStar_All.pipe_right uu____8866 (FStar_List.map (fun x -> (FStar_Util.split x "."))))))


let debug_any : unit  ->  Prims.bool = (fun uu____8892 -> (

let uu____8893 = (get_debug ())
in (Prims.op_disEquality uu____8893 [])))


let debug_module : Prims.string  ->  Prims.bool = (fun modul -> (

let uu____8910 = (get_debug ())
in (FStar_All.pipe_right uu____8910 (FStar_List.existsb (module_name_eq modul)))))


let debug_at_level : Prims.string  ->  debug_level_t  ->  Prims.bool = (fun modul level -> ((

let uu____8935 = (get_debug ())
in (FStar_All.pipe_right uu____8935 (FStar_List.existsb (module_name_eq modul)))) && (debug_level_geq level)))


let defensive : unit  ->  Prims.bool = (fun uu____8950 -> (

let uu____8951 = (get_defensive ())
in (Prims.op_disEquality uu____8951 "no")))


let defensive_fail : unit  ->  Prims.bool = (fun uu____8961 -> (

let uu____8962 = (get_defensive ())
in (Prims.op_Equality uu____8962 "fail")))


let dep : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____8974 -> (get_dep ()))


let detail_errors : unit  ->  Prims.bool = (fun uu____8981 -> (get_detail_errors ()))


let detail_hint_replay : unit  ->  Prims.bool = (fun uu____8988 -> (get_detail_hint_replay ()))


let doc : unit  ->  Prims.bool = (fun uu____8995 -> (get_doc ()))


let dump_module : Prims.string  ->  Prims.bool = (fun s -> (

let uu____9005 = (get_dump_module ())
in (FStar_All.pipe_right uu____9005 (FStar_List.existsb (module_name_eq s)))))


let eager_subtyping : unit  ->  Prims.bool = (fun uu____9020 -> (get_eager_subtyping ()))


let expose_interfaces : unit  ->  Prims.bool = (fun uu____9027 -> (get_expose_interfaces ()))


let fs_typ_app : Prims.string  ->  Prims.bool = (fun filename -> (

let uu____9037 = (FStar_ST.op_Bang light_off_files)
in (FStar_List.contains filename uu____9037)))


let full_context_dependency : unit  ->  Prims.bool = (fun uu____9073 -> true)


let hide_uvar_nums : unit  ->  Prims.bool = (fun uu____9081 -> (get_hide_uvar_nums ()))


let hint_info : unit  ->  Prims.bool = (fun uu____9088 -> ((get_hint_info ()) || (get_query_stats ())))


let hint_file : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____9097 -> (get_hint_file ()))


let ide : unit  ->  Prims.bool = (fun uu____9104 -> (get_ide ()))


let print : unit  ->  Prims.bool = (fun uu____9111 -> (get_print ()))


let print_in_place : unit  ->  Prims.bool = (fun uu____9118 -> (get_print_in_place ()))


let profile : 'a . (unit  ->  'a)  ->  ('a  ->  Prims.string)  ->  'a = (fun f msg -> (

let uu____9149 = (get_profile ())
in (match (uu____9149) with
| true -> begin
(

let uu____9152 = (FStar_Util.record_time f)
in (match (uu____9152) with
| (a, time) -> begin
((

let uu____9163 = (FStar_Util.string_of_int time)
in (

let uu____9165 = (msg a)
in (FStar_Util.print2 "Elapsed time %s ms: %s\n" uu____9163 uu____9165)));
a;
)
end))
end
| uu____9168 -> begin
(f ())
end)))


let initial_fuel : unit  ->  Prims.int = (fun uu____9176 -> (

let uu____9177 = (get_initial_fuel ())
in (

let uu____9179 = (get_max_fuel ())
in (Prims.min uu____9177 uu____9179))))


let initial_ifuel : unit  ->  Prims.int = (fun uu____9187 -> (

let uu____9188 = (get_initial_ifuel ())
in (

let uu____9190 = (get_max_ifuel ())
in (Prims.min uu____9188 uu____9190))))


let interactive : unit  ->  Prims.bool = (fun uu____9198 -> ((get_in ()) || (get_ide ())))


let lax : unit  ->  Prims.bool = (fun uu____9205 -> (get_lax ()))


let load : unit  ->  Prims.string Prims.list = (fun uu____9214 -> (get_load ()))


let legacy_interactive : unit  ->  Prims.bool = (fun uu____9221 -> (get_in ()))


let log_queries : unit  ->  Prims.bool = (fun uu____9228 -> (get_log_queries ()))


let keep_query_captions : unit  ->  Prims.bool = (fun uu____9235 -> ((log_queries ()) && (get_keep_query_captions ())))


let log_types : unit  ->  Prims.bool = (fun uu____9242 -> (get_log_types ()))


let max_fuel : unit  ->  Prims.int = (fun uu____9249 -> (get_max_fuel ()))


let max_ifuel : unit  ->  Prims.int = (fun uu____9256 -> (get_max_ifuel ()))


let min_fuel : unit  ->  Prims.int = (fun uu____9263 -> (get_min_fuel ()))


let ml_ish : unit  ->  Prims.bool = (fun uu____9270 -> (get_MLish ()))


let set_ml_ish : unit  ->  unit = (fun uu____9276 -> (set_option "MLish" (Bool (true))))


let n_cores : unit  ->  Prims.int = (fun uu____9285 -> (get_n_cores ()))


let no_default_includes : unit  ->  Prims.bool = (fun uu____9292 -> (get_no_default_includes ()))


let no_extract : Prims.string  ->  Prims.bool = (fun s -> (

let uu____9302 = (get_no_extract ())
in (FStar_All.pipe_right uu____9302 (FStar_List.existsb (module_name_eq s)))))


let normalize_pure_terms_for_extraction : unit  ->  Prims.bool = (fun uu____9317 -> (get_normalize_pure_terms_for_extraction ()))


let no_location_info : unit  ->  Prims.bool = (fun uu____9324 -> (get_no_location_info ()))


let no_plugins : unit  ->  Prims.bool = (fun uu____9331 -> (get_no_plugins ()))


let no_smt : unit  ->  Prims.bool = (fun uu____9338 -> (get_no_smt ()))


let output_dir : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____9347 -> (get_odir ()))


let ugly : unit  ->  Prims.bool = (fun uu____9354 -> (get_ugly ()))


let print_bound_var_types : unit  ->  Prims.bool = (fun uu____9361 -> (get_print_bound_var_types ()))


let print_effect_args : unit  ->  Prims.bool = (fun uu____9368 -> (get_print_effect_args ()))


let print_implicits : unit  ->  Prims.bool = (fun uu____9375 -> (get_print_implicits ()))


let print_real_names : unit  ->  Prims.bool = (fun uu____9382 -> ((get_prn ()) || (get_print_full_names ())))


let print_universes : unit  ->  Prims.bool = (fun uu____9389 -> (get_print_universes ()))


let print_z3_statistics : unit  ->  Prims.bool = (fun uu____9396 -> (get_print_z3_statistics ()))


let query_stats : unit  ->  Prims.bool = (fun uu____9403 -> (get_query_stats ()))


let record_hints : unit  ->  Prims.bool = (fun uu____9410 -> (get_record_hints ()))


let report_qi : unit  ->  Prims.bool = (fun uu____9417 -> (get_report_qi ()))


let reuse_hint_for : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____9426 -> (get_reuse_hint_for ()))


let silent : unit  ->  Prims.bool = (fun uu____9433 -> (get_silent ()))


let smtencoding_elim_box : unit  ->  Prims.bool = (fun uu____9440 -> (get_smtencoding_elim_box ()))


let smtencoding_nl_arith_native : unit  ->  Prims.bool = (fun uu____9447 -> (

let uu____9448 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____9448 "native")))


let smtencoding_nl_arith_wrapped : unit  ->  Prims.bool = (fun uu____9458 -> (

let uu____9459 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____9459 "wrapped")))


let smtencoding_nl_arith_default : unit  ->  Prims.bool = (fun uu____9469 -> (

let uu____9470 = (get_smtencoding_nl_arith_repr ())
in (Prims.op_Equality uu____9470 "boxwrap")))


let smtencoding_l_arith_native : unit  ->  Prims.bool = (fun uu____9480 -> (

let uu____9481 = (get_smtencoding_l_arith_repr ())
in (Prims.op_Equality uu____9481 "native")))


let smtencoding_l_arith_default : unit  ->  Prims.bool = (fun uu____9491 -> (

let uu____9492 = (get_smtencoding_l_arith_repr ())
in (Prims.op_Equality uu____9492 "boxwrap")))


let smtencoding_valid_intro : unit  ->  Prims.bool = (fun uu____9502 -> (get_smtencoding_valid_intro ()))


let smtencoding_valid_elim : unit  ->  Prims.bool = (fun uu____9509 -> (get_smtencoding_valid_elim ()))


let tactic_raw_binders : unit  ->  Prims.bool = (fun uu____9516 -> (get_tactic_raw_binders ()))


let tactics_failhard : unit  ->  Prims.bool = (fun uu____9523 -> (get_tactics_failhard ()))


let tactics_info : unit  ->  Prims.bool = (fun uu____9530 -> (get_tactics_info ()))


let tactic_trace : unit  ->  Prims.bool = (fun uu____9537 -> (get_tactic_trace ()))


let tactic_trace_d : unit  ->  Prims.int = (fun uu____9544 -> (get_tactic_trace_d ()))


let tactics_nbe : unit  ->  Prims.bool = (fun uu____9551 -> (get_tactics_nbe ()))


let tcnorm : unit  ->  Prims.bool = (fun uu____9558 -> (get_tcnorm ()))


let timing : unit  ->  Prims.bool = (fun uu____9565 -> (get_timing ()))


let trace_error : unit  ->  Prims.bool = (fun uu____9572 -> (get_trace_error ()))


let unthrottle_inductives : unit  ->  Prims.bool = (fun uu____9579 -> (get_unthrottle_inductives ()))


let unsafe_tactic_exec : unit  ->  Prims.bool = (fun uu____9586 -> (get_unsafe_tactic_exec ()))


let use_eq_at_higher_order : unit  ->  Prims.bool = (fun uu____9593 -> (get_use_eq_at_higher_order ()))


let use_hints : unit  ->  Prims.bool = (fun uu____9600 -> (get_use_hints ()))


let use_hint_hashes : unit  ->  Prims.bool = (fun uu____9607 -> (get_use_hint_hashes ()))


let use_native_tactics : unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____9616 -> (get_use_native_tactics ()))


let use_tactics : unit  ->  Prims.bool = (fun uu____9623 -> (get_use_tactics ()))


let using_facts_from : unit  ->  (Prims.string Prims.list * Prims.bool) Prims.list = (fun uu____9639 -> (

let uu____9640 = (get_using_facts_from ())
in (match (uu____9640) with
| FStar_Pervasives_Native.None -> begin
((([]), (true)))::[]
end
| FStar_Pervasives_Native.Some (ns) -> begin
(parse_settings ns)
end)))


let vcgen_optimize_bind_as_seq : unit  ->  Prims.bool = (fun uu____9694 -> (

let uu____9695 = (get_vcgen_optimize_bind_as_seq ())
in (FStar_Option.isSome uu____9695)))


let vcgen_decorate_with_type : unit  ->  Prims.bool = (fun uu____9706 -> (

let uu____9707 = (get_vcgen_optimize_bind_as_seq ())
in (match (uu____9707) with
| FStar_Pervasives_Native.Some ("with_type") -> begin
true
end
| uu____9715 -> begin
false
end)))


let warn_default_effects : unit  ->  Prims.bool = (fun uu____9726 -> (get_warn_default_effects ()))


let z3_exe : unit  ->  Prims.string = (fun uu____9733 -> (

let uu____9734 = (get_smt ())
in (match (uu____9734) with
| FStar_Pervasives_Native.None -> begin
(FStar_Platform.exe "z3")
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let z3_cliopt : unit  ->  Prims.string Prims.list = (fun uu____9752 -> (get_z3cliopt ()))


let z3_refresh : unit  ->  Prims.bool = (fun uu____9759 -> (get_z3refresh ()))


let z3_rlimit : unit  ->  Prims.int = (fun uu____9766 -> (get_z3rlimit ()))


let z3_rlimit_factor : unit  ->  Prims.int = (fun uu____9773 -> (get_z3rlimit_factor ()))


let z3_seed : unit  ->  Prims.int = (fun uu____9780 -> (get_z3seed ()))


let use_two_phase_tc : unit  ->  Prims.bool = (fun uu____9787 -> ((get_use_two_phase_tc ()) && (

let uu____9789 = (lax ())
in (not (uu____9789)))))


let no_positivity : unit  ->  Prims.bool = (fun uu____9797 -> (get_no_positivity ()))


let ml_no_eta_expand_coertions : unit  ->  Prims.bool = (fun uu____9804 -> (get_ml_no_eta_expand_coertions ()))


let warn_error : unit  ->  Prims.string = (fun uu____9811 -> (

let uu____9812 = (get_warn_error ())
in (FStar_String.concat "" uu____9812)))


let use_extracted_interfaces : unit  ->  Prims.bool = (fun uu____9823 -> (get_use_extracted_interfaces ()))


let use_nbe : unit  ->  Prims.bool = (fun uu____9830 -> (get_use_nbe ()))


let with_saved_options : 'a . (unit  ->  'a)  ->  'a = (fun f -> (

let uu____9847 = (

let uu____9849 = (trace_error ())
in (not (uu____9849)))
in (match (uu____9847) with
| true -> begin
((push ());
(

let r = (FStar_All.try_with (fun uu___724_9864 -> (match (()) with
| () -> begin
(

let uu____9869 = (f ())
in FStar_Util.Inr (uu____9869))
end)) (fun uu___723_9871 -> FStar_Util.Inl (uu___723_9871)))
in ((pop ());
(match (r) with
| FStar_Util.Inr (v1) -> begin
v1
end
| FStar_Util.Inl (ex) -> begin
(FStar_Exn.raise ex)
end);
));
)
end
| uu____9879 -> begin
((push ());
(

let retv = (f ())
in ((pop ());
retv;
));
)
end)))


let module_matches_namespace_filter : Prims.string  ->  Prims.string Prims.list  ->  Prims.bool = (fun m filter1 -> (

let m1 = (FStar_String.lowercase m)
in (

let setting = (parse_settings filter1)
in (

let m_components = (path_of_text m1)
in (

let rec matches_path = (fun m_components1 path -> (match (((m_components1), (path))) with
| (uu____9952, []) -> begin
true
end
| ((m2)::ms, (p)::ps) -> begin
((Prims.op_Equality m2 (FStar_String.lowercase p)) && (matches_path ms ps))
end
| uu____9985 -> begin
false
end))
in (

let uu____9997 = (FStar_All.pipe_right setting (FStar_Util.try_find (fun uu____10039 -> (match (uu____10039) with
| (path, uu____10050) -> begin
(matches_path m_components path)
end))))
in (match (uu____9997) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____10069, flag) -> begin
flag
end)))))))


let should_extract : Prims.string  ->  Prims.bool = (fun m -> (

let m1 = (FStar_String.lowercase m)
in (

let uu____10098 = (get_extract ())
in (match (uu____10098) with
| FStar_Pervasives_Native.Some (extract_setting) -> begin
((

let uu____10113 = (

let uu____10129 = (get_no_extract ())
in (

let uu____10133 = (get_extract_namespace ())
in (

let uu____10137 = (get_extract_module ())
in ((uu____10129), (uu____10133), (uu____10137)))))
in (match (uu____10113) with
| ([], [], []) -> begin
()
end
| uu____10162 -> begin
(failwith "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module")
end));
(module_matches_namespace_filter m1 extract_setting);
)
end
| FStar_Pervasives_Native.None -> begin
(

let should_extract_namespace = (fun m2 -> (

let uu____10191 = (get_extract_namespace ())
in (match (uu____10191) with
| [] -> begin
false
end
| ns -> begin
(FStar_All.pipe_right ns (FStar_Util.for_some (fun n1 -> (FStar_Util.starts_with m2 (FStar_String.lowercase n1)))))
end)))
in (

let should_extract_module = (fun m2 -> (

let uu____10219 = (get_extract_module ())
in (match (uu____10219) with
| [] -> begin
false
end
| l -> begin
(FStar_All.pipe_right l (FStar_Util.for_some (fun n1 -> (Prims.op_Equality (FStar_String.lowercase n1) m2))))
end)))
in ((

let uu____10241 = (no_extract m1)
in (not (uu____10241))) && (

let uu____10244 = (

let uu____10255 = (get_extract_namespace ())
in (

let uu____10259 = (get_extract_module ())
in ((uu____10255), (uu____10259))))
in (match (uu____10244) with
| ([], []) -> begin
true
end
| uu____10279 -> begin
((should_extract_namespace m1) || (should_extract_module m1))
end)))))
end))))


let should_be_already_cached : Prims.string  ->  Prims.bool = (fun m -> (

let uu____10299 = (get_already_cached ())
in (match (uu____10299) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (already_cached_setting) -> begin
(module_matches_namespace_filter m already_cached_setting)
end)))


let error_flags : unit  ->  error_flag Prims.list = (

let cache = (FStar_Util.smap_create (Prims.parse_int "10"))
in (fun uu____10332 -> (

let we = (warn_error ())
in (

let uu____10335 = (FStar_Util.smap_try_find cache we)
in (match (uu____10335) with
| FStar_Pervasives_Native.None -> begin
(

let r = (parse_warn_error we)
in ((FStar_Util.smap_add cache we r);
r;
))
end
| FStar_Pervasives_Native.Some (r) -> begin
r
end)))))




