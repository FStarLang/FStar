
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
| uu____65 -> begin
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
| uu____79 -> begin
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
| uu____93 -> begin
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
| uu____107 -> begin
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
| uu____122 -> begin
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
| uu____138 -> begin
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
| uu____143 -> begin
false
end))


let uu___is_Reset : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reset -> begin
true
end
| uu____148 -> begin
false
end))


let uu___is_Restore : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Restore -> begin
true
end
| uu____153 -> begin
false
end))


let __unit_tests__ : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let __unit_tests : Prims.unit  ->  Prims.bool = (fun uu____160 -> (FStar_ST.read __unit_tests__))


let __set_unit_tests : Prims.unit  ->  Prims.unit = (fun uu____166 -> (FStar_ST.write __unit_tests__ true))


let __clear_unit_tests : Prims.unit  ->  Prims.unit = (fun uu____172 -> (FStar_ST.write __unit_tests__ false))


let as_bool : option_val  ->  Prims.bool = (fun uu___49_178 -> (match (uu___49_178) with
| Bool (b) -> begin
b
end
| uu____180 -> begin
(failwith "Impos: expected Bool")
end))


let as_int : option_val  ->  Prims.int = (fun uu___50_184 -> (match (uu___50_184) with
| Int (b) -> begin
b
end
| uu____186 -> begin
(failwith "Impos: expected Int")
end))


let as_string : option_val  ->  Prims.string = (fun uu___51_190 -> (match (uu___51_190) with
| String (b) -> begin
b
end
| Path (b) -> begin
(FStar_Common.try_convert_file_name_to_mixed b)
end
| uu____193 -> begin
(failwith "Impos: expected String")
end))


let as_list = (fun as_t uu___52_212 -> (match (uu___52_212) with
| List (ts) -> begin
(FStar_All.pipe_right ts (FStar_List.map as_t))
end
| uu____219 -> begin
(failwith "Impos: expected List")
end))


let as_option = (fun as_t uu___53_239 -> (match (uu___53_239) with
| Unset -> begin
FStar_Pervasives_Native.None
end
| v1 -> begin
(

let uu____243 = (as_t v1)
in FStar_Pervasives_Native.Some (uu____243))
end))


type optionstate =
option_val FStar_Util.smap


let fstar_options : optionstate Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let peek : Prims.unit  ->  optionstate = (fun uu____253 -> (

let uu____254 = (FStar_ST.read fstar_options)
in (FStar_List.hd uu____254)))


let pop : Prims.unit  ->  Prims.unit = (fun uu____262 -> (

let uu____263 = (FStar_ST.read fstar_options)
in (match (uu____263) with
| [] -> begin
(failwith "TOO MANY POPS!")
end
| (uu____268)::[] -> begin
(failwith "TOO MANY POPS!")
end
| (uu____269)::tl1 -> begin
(FStar_ST.write fstar_options tl1)
end)))


let push : Prims.unit  ->  Prims.unit = (fun uu____278 -> (

let uu____279 = (

let uu____281 = (

let uu____283 = (peek ())
in (FStar_Util.smap_copy uu____283))
in (

let uu____285 = (FStar_ST.read fstar_options)
in (uu____281)::uu____285))
in (FStar_ST.write fstar_options uu____279)))


let set : optionstate  ->  Prims.unit = (fun o -> (

let uu____299 = (FStar_ST.read fstar_options)
in (match (uu____299) with
| [] -> begin
(failwith "set on empty option stack")
end
| (uu____304)::os -> begin
(FStar_ST.write fstar_options ((o)::os))
end)))


let set_option : Prims.string  ->  option_val  ->  Prims.unit = (fun k v1 -> (

let uu____318 = (peek ())
in (FStar_Util.smap_add uu____318 k v1)))


let set_option' : (Prims.string * option_val)  ->  Prims.unit = (fun uu____325 -> (match (uu____325) with
| (k, v1) -> begin
(set_option k v1)
end))


let with_saved_options = (fun f -> ((push ());
(

let retv = (f ())
in ((pop ());
retv;
));
))


let light_off_files : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let add_light_off_file : Prims.string  ->  Prims.unit = (fun filename -> (

let uu____356 = (

let uu____358 = (FStar_ST.read light_off_files)
in (filename)::uu____358)
in (FStar_ST.write light_off_files uu____356)))


let defaults : (Prims.string * option_val) Prims.list = ((("__temp_no_proj"), (List ([]))))::((("_fstar_home"), (String (""))))::((("_include_path"), (List ([]))))::((("admit_smt_queries"), (Bool (false))))::((("check_hints"), (Bool (false))))::((("codegen"), (Unset)))::((("codegen-lib"), (List ([]))))::((("debug"), (List ([]))))::((("debug_level"), (List ([]))))::((("dep"), (Unset)))::((("detail_errors"), (Bool (false))))::((("doc"), (Bool (false))))::((("dump_module"), (List ([]))))::((("eager_inference"), (Bool (false))))::((("explicit_deps"), (Bool (false))))::((("extract_all"), (Bool (false))))::((("extract_module"), (List ([]))))::((("extract_namespace"), (List ([]))))::((("fs_typ_app"), (Bool (false))))::((("fstar_home"), (Unset)))::((("full_context_dependency"), (Bool (true))))::((("hide_genident_nums"), (Bool (false))))::((("hide_uvar_nums"), (Bool (false))))::((("hint_info"), (Bool (false))))::((("hint_file"), (Unset)))::((("in"), (Bool (false))))::((("ide"), (Bool (false))))::((("include"), (List ([]))))::((("indent"), (Bool (false))))::((("initial_fuel"), (Int ((Prims.parse_int "2")))))::((("initial_ifuel"), (Int ((Prims.parse_int "1")))))::((("lax"), (Bool (false))))::((("load"), (List ([]))))::((("log_queries"), (Bool (false))))::((("log_types"), (Bool (false))))::((("max_fuel"), (Int ((Prims.parse_int "8")))))::((("max_ifuel"), (Int ((Prims.parse_int "2")))))::((("min_fuel"), (Int ((Prims.parse_int "1")))))::((("MLish"), (Bool (false))))::((("n_cores"), (Int ((Prims.parse_int "1")))))::((("no_default_includes"), (Bool (false))))::((("no_extract"), (List ([]))))::((("no_location_info"), (Bool (false))))::((("odir"), (Unset)))::((("prims"), (Unset)))::((("pretype"), (Bool (true))))::((("prims_ref"), (Unset)))::((("print_bound_var_types"), (Bool (false))))::((("print_effect_args"), (Bool (false))))::((("print_fuels"), (Bool (false))))::((("print_full_names"), (Bool (false))))::((("print_implicits"), (Bool (false))))::((("print_universes"), (Bool (false))))::((("print_z3_statistics"), (Bool (false))))::((("prn"), (Bool (false))))::((("record_hints"), (Bool (false))))::((("reuse_hint_for"), (Unset)))::((("show_signatures"), (List ([]))))::((("silent"), (Bool (false))))::((("smt"), (Unset)))::((("smtencoding.elim_box"), (Bool (false))))::((("smtencoding.nl_arith_repr"), (String ("boxwrap"))))::((("smtencoding.l_arith_repr"), (String ("boxwrap"))))::((("split_cases"), (Int ((Prims.parse_int "0")))))::((("timing"), (Bool (false))))::((("trace_error"), (Bool (false))))::((("ugly"), (Bool (false))))::((("unthrottle_inductives"), (Bool (false))))::((("use_eq_at_higher_order"), (Bool (false))))::((("use_hints"), (Bool (false))))::((("no_tactics"), (Bool (false))))::((("using_facts_from"), (Unset)))::((("verify"), (Bool (true))))::((("verify_all"), (Bool (false))))::((("verify_module"), (List ([]))))::((("warn_default_effects"), (Bool (false))))::((("z3refresh"), (Bool (false))))::((("z3rlimit"), (Int ((Prims.parse_int "5")))))::((("z3rlimit_factor"), (Int ((Prims.parse_int "1")))))::((("z3seed"), (Int ((Prims.parse_int "0")))))::((("z3cliopt"), (List ([]))))::((("__no_positivity"), (Bool (false))))::[]


let init : Prims.unit  ->  Prims.unit = (fun uu____538 -> (

let o = (peek ())
in ((FStar_Util.smap_clear o);
(FStar_All.pipe_right defaults (FStar_List.iter set_option'));
)))


let clear : Prims.unit  ->  Prims.unit = (fun uu____549 -> (

let o = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_ST.write fstar_options ((o)::[]));
(FStar_ST.write light_off_files []);
(init ());
)))


let _run : Prims.unit = (clear ())


let get_option : Prims.string  ->  option_val = (fun s -> (

let uu____566 = (

let uu____568 = (peek ())
in (FStar_Util.smap_try_find uu____568 s))
in (match (uu____566) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Impossible: option " (Prims.strcat s " not found")))
end
| FStar_Pervasives_Native.Some (s1) -> begin
s1
end)))


let lookup_opt = (fun s c -> (c (get_option s)))


let get_admit_smt_queries : Prims.unit  ->  Prims.bool = (fun uu____594 -> (lookup_opt "admit_smt_queries" as_bool))


let get_check_hints : Prims.unit  ->  Prims.bool = (fun uu____598 -> (lookup_opt "check_hints" as_bool))


let get_codegen : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____603 -> (lookup_opt "codegen" (as_option as_string)))


let get_codegen_lib : Prims.unit  ->  Prims.string Prims.list = (fun uu____609 -> (lookup_opt "codegen-lib" (as_list as_string)))


let get_debug : Prims.unit  ->  Prims.string Prims.list = (fun uu____615 -> (lookup_opt "debug" (as_list as_string)))


let get_debug_level : Prims.unit  ->  Prims.string Prims.list = (fun uu____621 -> (lookup_opt "debug_level" (as_list as_string)))


let get_dep : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____627 -> (lookup_opt "dep" (as_option as_string)))


let get_detail_errors : Prims.unit  ->  Prims.bool = (fun uu____632 -> (lookup_opt "detail_errors" as_bool))


let get_doc : Prims.unit  ->  Prims.bool = (fun uu____636 -> (lookup_opt "doc" as_bool))


let get_dump_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____641 -> (lookup_opt "dump_module" (as_list as_string)))


let get_eager_inference : Prims.unit  ->  Prims.bool = (fun uu____646 -> (lookup_opt "eager_inference" as_bool))


let get_explicit_deps : Prims.unit  ->  Prims.bool = (fun uu____650 -> (lookup_opt "explicit_deps" as_bool))


let get_extract_all : Prims.unit  ->  Prims.bool = (fun uu____654 -> (lookup_opt "extract_all" as_bool))


let get_extract_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____659 -> (lookup_opt "extract_module" (as_list as_string)))


let get_extract_namespace : Prims.unit  ->  Prims.string Prims.list = (fun uu____665 -> (lookup_opt "extract_namespace" (as_list as_string)))


let get_fs_typ_app : Prims.unit  ->  Prims.bool = (fun uu____670 -> (lookup_opt "fs_typ_app" as_bool))


let get_fstar_home : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____675 -> (lookup_opt "fstar_home" (as_option as_string)))


let get_hide_genident_nums : Prims.unit  ->  Prims.bool = (fun uu____680 -> (lookup_opt "hide_genident_nums" as_bool))


let get_hide_uvar_nums : Prims.unit  ->  Prims.bool = (fun uu____684 -> (lookup_opt "hide_uvar_nums" as_bool))


let get_hint_info : Prims.unit  ->  Prims.bool = (fun uu____688 -> (lookup_opt "hint_info" as_bool))


let get_hint_file : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____693 -> (lookup_opt "hint_file" (as_option as_string)))


let get_in : Prims.unit  ->  Prims.bool = (fun uu____698 -> (lookup_opt "in" as_bool))


let get_ide : Prims.unit  ->  Prims.bool = (fun uu____702 -> (lookup_opt "ide" as_bool))


let get_include : Prims.unit  ->  Prims.string Prims.list = (fun uu____707 -> (lookup_opt "include" (as_list as_string)))


let get_indent : Prims.unit  ->  Prims.bool = (fun uu____712 -> (lookup_opt "indent" as_bool))


let get_initial_fuel : Prims.unit  ->  Prims.int = (fun uu____716 -> (lookup_opt "initial_fuel" as_int))


let get_initial_ifuel : Prims.unit  ->  Prims.int = (fun uu____720 -> (lookup_opt "initial_ifuel" as_int))


let get_lax : Prims.unit  ->  Prims.bool = (fun uu____724 -> (lookup_opt "lax" as_bool))


let get_load : Prims.unit  ->  Prims.string Prims.list = (fun uu____729 -> (lookup_opt "load" (as_list as_string)))


let get_log_queries : Prims.unit  ->  Prims.bool = (fun uu____734 -> (lookup_opt "log_queries" as_bool))


let get_log_types : Prims.unit  ->  Prims.bool = (fun uu____738 -> (lookup_opt "log_types" as_bool))


let get_max_fuel : Prims.unit  ->  Prims.int = (fun uu____742 -> (lookup_opt "max_fuel" as_int))


let get_max_ifuel : Prims.unit  ->  Prims.int = (fun uu____746 -> (lookup_opt "max_ifuel" as_int))


let get_min_fuel : Prims.unit  ->  Prims.int = (fun uu____750 -> (lookup_opt "min_fuel" as_int))


let get_MLish : Prims.unit  ->  Prims.bool = (fun uu____754 -> (lookup_opt "MLish" as_bool))


let get_n_cores : Prims.unit  ->  Prims.int = (fun uu____758 -> (lookup_opt "n_cores" as_int))


let get_no_default_includes : Prims.unit  ->  Prims.bool = (fun uu____762 -> (lookup_opt "no_default_includes" as_bool))


let get_no_extract : Prims.unit  ->  Prims.string Prims.list = (fun uu____767 -> (lookup_opt "no_extract" (as_list as_string)))


let get_no_location_info : Prims.unit  ->  Prims.bool = (fun uu____772 -> (lookup_opt "no_location_info" as_bool))


let get_odir : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____777 -> (lookup_opt "odir" (as_option as_string)))


let get_ugly : Prims.unit  ->  Prims.bool = (fun uu____782 -> (lookup_opt "ugly" as_bool))


let get_prims : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____787 -> (lookup_opt "prims" (as_option as_string)))


let get_print_bound_var_types : Prims.unit  ->  Prims.bool = (fun uu____792 -> (lookup_opt "print_bound_var_types" as_bool))


let get_print_effect_args : Prims.unit  ->  Prims.bool = (fun uu____796 -> (lookup_opt "print_effect_args" as_bool))


let get_print_fuels : Prims.unit  ->  Prims.bool = (fun uu____800 -> (lookup_opt "print_fuels" as_bool))


let get_print_full_names : Prims.unit  ->  Prims.bool = (fun uu____804 -> (lookup_opt "print_full_names" as_bool))


let get_print_implicits : Prims.unit  ->  Prims.bool = (fun uu____808 -> (lookup_opt "print_implicits" as_bool))


let get_print_universes : Prims.unit  ->  Prims.bool = (fun uu____812 -> (lookup_opt "print_universes" as_bool))


let get_print_z3_statistics : Prims.unit  ->  Prims.bool = (fun uu____816 -> (lookup_opt "print_z3_statistics" as_bool))


let get_prn : Prims.unit  ->  Prims.bool = (fun uu____820 -> (lookup_opt "prn" as_bool))


let get_record_hints : Prims.unit  ->  Prims.bool = (fun uu____824 -> (lookup_opt "record_hints" as_bool))


let get_reuse_hint_for : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____829 -> (lookup_opt "reuse_hint_for" (as_option as_string)))


let get_show_signatures : Prims.unit  ->  Prims.string Prims.list = (fun uu____835 -> (lookup_opt "show_signatures" (as_list as_string)))


let get_silent : Prims.unit  ->  Prims.bool = (fun uu____840 -> (lookup_opt "silent" as_bool))


let get_smt : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____845 -> (lookup_opt "smt" (as_option as_string)))


let get_smtencoding_elim_box : Prims.unit  ->  Prims.bool = (fun uu____850 -> (lookup_opt "smtencoding.elim_box" as_bool))


let get_smtencoding_nl_arith_repr : Prims.unit  ->  Prims.string = (fun uu____854 -> (lookup_opt "smtencoding.nl_arith_repr" as_string))


let get_smtencoding_l_arith_repr : Prims.unit  ->  Prims.string = (fun uu____858 -> (lookup_opt "smtencoding.l_arith_repr" as_string))


let get_split_cases : Prims.unit  ->  Prims.int = (fun uu____862 -> (lookup_opt "split_cases" as_int))


let get_timing : Prims.unit  ->  Prims.bool = (fun uu____866 -> (lookup_opt "timing" as_bool))


let get_trace_error : Prims.unit  ->  Prims.bool = (fun uu____870 -> (lookup_opt "trace_error" as_bool))


let get_unthrottle_inductives : Prims.unit  ->  Prims.bool = (fun uu____874 -> (lookup_opt "unthrottle_inductives" as_bool))


let get_use_eq_at_higher_order : Prims.unit  ->  Prims.bool = (fun uu____878 -> (lookup_opt "use_eq_at_higher_order" as_bool))


let get_use_hints : Prims.unit  ->  Prims.bool = (fun uu____882 -> (lookup_opt "use_hints" as_bool))


let get_use_tactics : Prims.unit  ->  Prims.bool = (fun uu____886 -> (

let uu____887 = (lookup_opt "no_tactics" as_bool)
in (not (uu____887))))


let get_using_facts_from : Prims.unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____893 -> (lookup_opt "using_facts_from" (as_option (as_list as_string))))


let get_verify_all : Prims.unit  ->  Prims.bool = (fun uu____900 -> (lookup_opt "verify_all" as_bool))


let get_verify_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____905 -> (lookup_opt "verify_module" (as_list as_string)))


let get___temp_no_proj : Prims.unit  ->  Prims.string Prims.list = (fun uu____911 -> (lookup_opt "__temp_no_proj" (as_list as_string)))


let get_version : Prims.unit  ->  Prims.bool = (fun uu____916 -> (lookup_opt "version" as_bool))


let get_warn_default_effects : Prims.unit  ->  Prims.bool = (fun uu____920 -> (lookup_opt "warn_default_effects" as_bool))


let get_z3cliopt : Prims.unit  ->  Prims.string Prims.list = (fun uu____925 -> (lookup_opt "z3cliopt" (as_list as_string)))


let get_z3refresh : Prims.unit  ->  Prims.bool = (fun uu____930 -> (lookup_opt "z3refresh" as_bool))


let get_z3rlimit : Prims.unit  ->  Prims.int = (fun uu____934 -> (lookup_opt "z3rlimit" as_int))


let get_z3rlimit_factor : Prims.unit  ->  Prims.int = (fun uu____938 -> (lookup_opt "z3rlimit_factor" as_int))


let get_z3seed : Prims.unit  ->  Prims.int = (fun uu____942 -> (lookup_opt "z3seed" as_int))


let get_no_positivity : Prims.unit  ->  Prims.bool = (fun uu____946 -> (lookup_opt "__no_positivity" as_bool))


let dlevel : Prims.string  ->  debug_level_t = (fun uu___54_950 -> (match (uu___54_950) with
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
| Other (uu____960) -> begin
(l1 = l2)
end
| Low -> begin
(l1 = l2)
end
| Medium -> begin
((l2 = Low) || (l2 = Medium))
end
| High -> begin
(((l2 = Low) || (l2 = Medium)) || (l2 = High))
end
| Extreme -> begin
((((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme))
end))


let debug_level_geq : debug_level_t  ->  Prims.bool = (fun l2 -> (

let uu____965 = (get_debug_level ())
in (FStar_All.pipe_right uu____965 (FStar_Util.for_some (fun l1 -> (one_debug_level_geq (dlevel l1) l2))))))


let universe_include_path_base_dirs : Prims.string Prims.list = ("/ulib")::("/lib/fstar")::[]


let _version : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _platform : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _compiler : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _date : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _commit : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let display_version : Prims.unit  ->  Prims.unit = (fun uu____994 -> (

let uu____995 = (

let uu____996 = (FStar_ST.read _version)
in (

let uu____999 = (FStar_ST.read _platform)
in (

let uu____1002 = (FStar_ST.read _compiler)
in (

let uu____1005 = (FStar_ST.read _date)
in (

let uu____1008 = (FStar_ST.read _commit)
in (FStar_Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____996 uu____999 uu____1002 uu____1005 uu____1008))))))
in (FStar_Util.print_string uu____995)))


let display_usage_aux = (fun specs -> ((FStar_Util.print_string "fstar.exe [options] file[s]\n");
(FStar_List.iter (fun uu____1048 -> (match (uu____1048) with
| (uu____1054, flag, p, doc) -> begin
(match (p) with
| FStar_Getopt.ZeroArgs (ig) -> begin
(match ((doc = "")) with
| true -> begin
(

let uu____1063 = (

let uu____1064 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format1 "  --%s\n" uu____1064))
in (FStar_Util.print_string uu____1063))
end
| uu____1065 -> begin
(

let uu____1066 = (

let uu____1067 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format2 "  --%s  %s\n" uu____1067 doc))
in (FStar_Util.print_string uu____1066))
end)
end
| FStar_Getopt.OneArg (uu____1068, argname) -> begin
(match ((doc = "")) with
| true -> begin
(

let uu____1074 = (

let uu____1075 = (FStar_Util.colorize_bold flag)
in (

let uu____1076 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format2 "  --%s %s\n" uu____1075 uu____1076)))
in (FStar_Util.print_string uu____1074))
end
| uu____1077 -> begin
(

let uu____1078 = (

let uu____1079 = (FStar_Util.colorize_bold flag)
in (

let uu____1080 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format3 "  --%s %s  %s\n" uu____1079 uu____1080 doc)))
in (FStar_Util.print_string uu____1078))
end)
end)
end)) specs);
))


let mk_spec : (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant * Prims.string)  ->  FStar_Getopt.opt = (fun o -> (

let uu____1095 = o
in (match (uu____1095) with
| (ns, name, arg, desc) -> begin
(

let arg1 = (match (arg) with
| FStar_Getopt.ZeroArgs (f) -> begin
(

let g = (fun uu____1116 -> (

let uu____1117 = (

let uu____1120 = (f ())
in ((name), (uu____1120)))
in (set_option' uu____1117)))
in FStar_Getopt.ZeroArgs (g))
end
| FStar_Getopt.OneArg (f, d) -> begin
(

let g = (fun x -> (

let uu____1131 = (

let uu____1134 = (f x)
in ((name), (uu____1134)))
in (set_option' uu____1131)))
in FStar_Getopt.OneArg (((g), (d))))
end)
in ((ns), (name), (arg1), (desc)))
end)))


let cons_extract_module : Prims.string  ->  option_val = (fun s -> (

let uu____1142 = (

let uu____1144 = (

let uu____1146 = (get_extract_module ())
in ((FStar_String.lowercase s))::uu____1146)
in (FStar_All.pipe_right uu____1144 (FStar_List.map (fun _0_26 -> String (_0_26)))))
in List (uu____1142)))


let cons_extract_namespace : Prims.string  ->  option_val = (fun s -> (

let uu____1154 = (

let uu____1156 = (

let uu____1158 = (get_extract_namespace ())
in ((FStar_String.lowercase s))::uu____1158)
in (FStar_All.pipe_right uu____1156 (FStar_List.map (fun _0_27 -> String (_0_27)))))
in List (uu____1154)))


let add_extract_module : Prims.string  ->  Prims.unit = (fun s -> (

let uu____1166 = (cons_extract_module s)
in (set_option "extract_module" uu____1166)))


let add_extract_namespace : Prims.string  ->  Prims.unit = (fun s -> (

let uu____1171 = (cons_extract_namespace s)
in (set_option "extract_namespace" uu____1171)))


let cons_verify_module : Prims.string  ->  option_val = (fun s -> (

let uu____1176 = (

let uu____1178 = (

let uu____1180 = (get_verify_module ())
in ((FStar_String.lowercase s))::uu____1180)
in (FStar_All.pipe_right uu____1178 (FStar_List.map (fun _0_28 -> String (_0_28)))))
in List (uu____1176)))


let cons_using_facts_from : Prims.string  ->  option_val = (fun s -> ((set_option "z3refresh" (Bool (true)));
(

let uu____1189 = (get_using_facts_from ())
in (match (uu____1189) with
| FStar_Pervasives_Native.None -> begin
List ((String (s))::[])
end
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____1196 = (FStar_List.map (fun _0_29 -> String (_0_29)) ((s)::l))
in List (uu____1196))
end));
))


let add_verify_module : Prims.string  ->  Prims.unit = (fun s -> (

let uu____1202 = (cons_verify_module s)
in (set_option "verify_module" uu____1202)))


let rec specs : Prims.unit  ->  FStar_Getopt.opt Prims.list = (fun uu____1214 -> (

let specs1 = (((FStar_Getopt.noshort), ("admit_smt_queries"), (FStar_Getopt.OneArg ((((fun s -> (match ((s = "true")) with
| true -> begin
Bool (true)
end
| uu____1233 -> begin
(match ((s = "false")) with
| true -> begin
Bool (false)
end
| uu____1234 -> begin
(failwith "Invalid argument to --admit_smt_queries")
end)
end))), ("[true|false]")))), ("Admit SMT queries, unsafe! (default \'false\')")))::(((FStar_Getopt.noshort), ("codegen"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1246 = (parse_codegen s)
in String (uu____1246)))), ("[OCaml|FSharp|Kremlin]")))), ("Generate code for execution")))::(((FStar_Getopt.noshort), ("codegen-lib"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1258 = (

let uu____1260 = (

let uu____1262 = (get_codegen_lib ())
in (s)::uu____1262)
in (FStar_All.pipe_right uu____1260 (FStar_List.map (fun _0_30 -> String (_0_30)))))
in List (uu____1258)))), ("[namespace]")))), ("External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")))::(((FStar_Getopt.noshort), ("debug"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1277 = (

let uu____1279 = (

let uu____1281 = (get_debug ())
in (x)::uu____1281)
in (FStar_All.pipe_right uu____1279 (FStar_List.map (fun _0_31 -> String (_0_31)))))
in List (uu____1277)))), ("[module name]")))), ("Print lots of debugging information while checking module")))::(((FStar_Getopt.noshort), ("debug_level"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1296 = (

let uu____1298 = (

let uu____1300 = (get_debug_level ())
in (x)::uu____1300)
in (FStar_All.pipe_right uu____1298 (FStar_List.map (fun _0_32 -> String (_0_32)))))
in List (uu____1296)))), ("[Low|Medium|High|Extreme|...]")))), ("Control the verbosity of debugging info")))::(((FStar_Getopt.noshort), ("dep"), (FStar_Getopt.OneArg ((((fun x -> (match (((x = "make") || (x = "graph"))) with
| true -> begin
String (x)
end
| uu____1314 -> begin
(failwith "invalid argument to \'dep\'")
end))), ("[make|graph]")))), ("Output the transitive closure of the dependency graph in a format suitable for the given tool")))::(((FStar_Getopt.noshort), ("detail_errors"), (FStar_Getopt.ZeroArgs ((fun uu____1322 -> Bool (true)))), ("Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")))::(((FStar_Getopt.noshort), ("doc"), (FStar_Getopt.ZeroArgs ((fun uu____1330 -> Bool (true)))), ("Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")))::(((FStar_Getopt.noshort), ("dump_module"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1342 = (

let uu____1344 = (

let uu____1346 = (get_dump_module ())
in (x)::uu____1346)
in (FStar_All.pipe_right uu____1344 (FStar_List.map (fun _0_33 -> String (_0_33)))))
in (FStar_All.pipe_right uu____1342 (fun _0_34 -> List (_0_34)))))), ("[module name]")))), ("")))::(((FStar_Getopt.noshort), ("eager_inference"), (FStar_Getopt.ZeroArgs ((fun uu____1358 -> Bool (true)))), ("Solve all type-inference constraints eagerly; more efficient but at the cost of generality")))::(((FStar_Getopt.noshort), ("explicit_deps"), (FStar_Getopt.ZeroArgs ((fun uu____1366 -> Bool (true)))), ("Do not find dependencies automatically, the user provides them on the command-line")))::(((FStar_Getopt.noshort), ("extract_all"), (FStar_Getopt.ZeroArgs ((fun uu____1374 -> Bool (true)))), ("Discover the complete dependency graph and do not stop at interface boundaries")))::(((FStar_Getopt.noshort), ("extract_module"), (FStar_Getopt.OneArg (((cons_extract_module), ("[module name]")))), ("Only extract the specified modules (instead of the possibly-partial dependency graph)")))::(((FStar_Getopt.noshort), ("extract_namespace"), (FStar_Getopt.OneArg (((cons_extract_namespace), ("[namespace name]")))), ("Only extract modules in the specified namespace")))::(((FStar_Getopt.noshort), ("fstar_home"), (FStar_Getopt.OneArg ((((fun _0_35 -> Path (_0_35))), ("[dir]")))), ("Set the FSTAR_HOME variable to [dir]")))::(((FStar_Getopt.noshort), ("hide_genident_nums"), (FStar_Getopt.ZeroArgs ((fun uu____1406 -> Bool (true)))), ("Don\'t print generated identifier numbers")))::(((FStar_Getopt.noshort), ("hide_uvar_nums"), (FStar_Getopt.ZeroArgs ((fun uu____1414 -> Bool (true)))), ("Don\'t print unification variable numbers")))::(((FStar_Getopt.noshort), ("hint_info"), (FStar_Getopt.ZeroArgs ((fun uu____1422 -> Bool (true)))), ("Print information regarding hints")))::(((FStar_Getopt.noshort), ("hint_file"), (FStar_Getopt.OneArg ((((fun _0_36 -> Path (_0_36))), ("[path]")))), ("Read/write hints to <path> (instead of module-specific hints files)")))::(((FStar_Getopt.noshort), ("in"), (FStar_Getopt.ZeroArgs ((fun uu____1438 -> Bool (true)))), ("Legacy interactive mode; reads input from stdin")))::(((FStar_Getopt.noshort), ("ide"), (FStar_Getopt.ZeroArgs ((fun uu____1446 -> Bool (true)))), ("JSON-based interactive mode for IDEs")))::(((FStar_Getopt.noshort), ("include"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1458 = (

let uu____1460 = (

let uu____1462 = (get_include ())
in (FStar_List.map (fun _0_37 -> String (_0_37)) uu____1462))
in (FStar_List.append uu____1460 ((Path (s))::[])))
in List (uu____1458)))), ("[path]")))), ("A directory in which to search for files included on the command line")))::(((FStar_Getopt.noshort), ("indent"), (FStar_Getopt.ZeroArgs ((fun uu____1471 -> Bool (true)))), ("Parses and outputs the files on the command line")))::(((FStar_Getopt.noshort), ("initial_fuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1483 = (FStar_Util.int_of_string x)
in Int (uu____1483)))), ("[non-negative integer]")))), ("Number of unrolling of recursive functions to try initially (default 2)")))::(((FStar_Getopt.noshort), ("initial_ifuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1495 = (FStar_Util.int_of_string x)
in Int (uu____1495)))), ("[non-negative integer]")))), ("Number of unrolling of inductive datatypes to try at first (default 1)")))::(((FStar_Getopt.noshort), ("inline_arith"), (FStar_Getopt.ZeroArgs ((fun uu____1503 -> Bool (true)))), ("Inline definitions of arithmetic functions in the SMT encoding")))::(((FStar_Getopt.noshort), ("lax"), (FStar_Getopt.ZeroArgs ((fun uu____1511 -> Bool (true)))), ("Run the lax-type checker only (admit all verification conditions)")))::(((FStar_Getopt.noshort), ("load"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1523 = (

let uu____1525 = (

let uu____1527 = (get_load ())
in (FStar_List.map (fun _0_38 -> String (_0_38)) uu____1527))
in (FStar_List.append uu____1525 ((Path (s))::[])))
in List (uu____1523)))), ("[module]")))), ("Load compiled module")))::(((FStar_Getopt.noshort), ("log_types"), (FStar_Getopt.ZeroArgs ((fun uu____1536 -> Bool (true)))), ("Print types computed for data/val/let-bindings")))::(((FStar_Getopt.noshort), ("log_queries"), (FStar_Getopt.ZeroArgs ((fun uu____1544 -> Bool (true)))), ("Log the Z3 queries in several queries-*.smt2 files, as we go")))::(((FStar_Getopt.noshort), ("max_fuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1556 = (FStar_Util.int_of_string x)
in Int (uu____1556)))), ("[non-negative integer]")))), ("Number of unrolling of recursive functions to try at most (default 8)")))::(((FStar_Getopt.noshort), ("max_ifuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1568 = (FStar_Util.int_of_string x)
in Int (uu____1568)))), ("[non-negative integer]")))), ("Number of unrolling of inductive datatypes to try at most (default 2)")))::(((FStar_Getopt.noshort), ("min_fuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1580 = (FStar_Util.int_of_string x)
in Int (uu____1580)))), ("[non-negative integer]")))), ("Minimum number of unrolling of recursive functions to try (default 1)")))::(((FStar_Getopt.noshort), ("MLish"), (FStar_Getopt.ZeroArgs ((fun uu____1588 -> Bool (true)))), ("Trigger various specializations for compiling the F* compiler itself (not meant for user code)")))::(((FStar_Getopt.noshort), ("n_cores"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1600 = (FStar_Util.int_of_string x)
in Int (uu____1600)))), ("[positive integer]")))), ("Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")))::(((FStar_Getopt.noshort), ("no_default_includes"), (FStar_Getopt.ZeroArgs ((fun uu____1608 -> Bool (true)))), ("Ignore the default module search paths")))::(((FStar_Getopt.noshort), ("no_extract"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1620 = (

let uu____1622 = (

let uu____1624 = (get_no_extract ())
in (x)::uu____1624)
in (FStar_All.pipe_right uu____1622 (FStar_List.map (fun _0_39 -> String (_0_39)))))
in List (uu____1620)))), ("[module name]")))), ("Do not extract code from this module")))::(((FStar_Getopt.noshort), ("no_location_info"), (FStar_Getopt.ZeroArgs ((fun uu____1635 -> Bool (true)))), ("Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")))::(((FStar_Getopt.noshort), ("odir"), (FStar_Getopt.OneArg ((((fun p -> (

let uu____1647 = (validate_dir p)
in Path (uu____1647)))), ("[dir]")))), ("Place output in directory [dir]")))::(((FStar_Getopt.noshort), ("prims"), (FStar_Getopt.OneArg ((((fun _0_40 -> String (_0_40))), ("file")))), ("")))::(((FStar_Getopt.noshort), ("print_bound_var_types"), (FStar_Getopt.ZeroArgs ((fun uu____1663 -> Bool (true)))), ("Print the types of bound variables")))::(((FStar_Getopt.noshort), ("print_effect_args"), (FStar_Getopt.ZeroArgs ((fun uu____1671 -> Bool (true)))), ("Print inferred predicate transformers for all computation types")))::(((FStar_Getopt.noshort), ("print_fuels"), (FStar_Getopt.ZeroArgs ((fun uu____1679 -> Bool (true)))), ("Print the fuel amounts used for each successful query")))::(((FStar_Getopt.noshort), ("print_full_names"), (FStar_Getopt.ZeroArgs ((fun uu____1687 -> Bool (true)))), ("Print full names of variables")))::(((FStar_Getopt.noshort), ("print_implicits"), (FStar_Getopt.ZeroArgs ((fun uu____1695 -> Bool (true)))), ("Print implicit arguments")))::(((FStar_Getopt.noshort), ("print_universes"), (FStar_Getopt.ZeroArgs ((fun uu____1703 -> Bool (true)))), ("Print universes")))::(((FStar_Getopt.noshort), ("print_z3_statistics"), (FStar_Getopt.ZeroArgs ((fun uu____1711 -> Bool (true)))), ("Print Z3 statistics for each SMT query")))::(((FStar_Getopt.noshort), ("prn"), (FStar_Getopt.ZeroArgs ((fun uu____1719 -> Bool (true)))), ("Print full names (deprecated; use --print_full_names instead)")))::(((FStar_Getopt.noshort), ("record_hints"), (FStar_Getopt.ZeroArgs ((fun uu____1727 -> Bool (true)))), ("Record a database of hints for efficient proof replay")))::(((FStar_Getopt.noshort), ("check_hints"), (FStar_Getopt.ZeroArgs ((fun uu____1735 -> Bool (true)))), ("Check new hints for replayability")))::(((FStar_Getopt.noshort), ("reuse_hint_for"), (FStar_Getopt.OneArg ((((fun _0_41 -> String (_0_41))), ("top-level name in the current module")))), ("Optimistically, attempt using the recorded hint for \'f\' when trying to verify some other term \'g\'")))::(((FStar_Getopt.noshort), ("show_signatures"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1755 = (

let uu____1757 = (

let uu____1759 = (get_show_signatures ())
in (x)::uu____1759)
in (FStar_All.pipe_right uu____1757 (FStar_List.map (fun _0_42 -> String (_0_42)))))
in List (uu____1755)))), ("[module name]")))), ("Show the checked signatures for all top-level symbols in the module")))::(((FStar_Getopt.noshort), ("silent"), (FStar_Getopt.ZeroArgs ((fun uu____1770 -> Bool (true)))), (" ")))::(((FStar_Getopt.noshort), ("smt"), (FStar_Getopt.OneArg ((((fun _0_43 -> Path (_0_43))), ("[path]")))), ("Path to the Z3 SMT solver (we could eventually support other solvers)")))::(((FStar_Getopt.noshort), ("smtencoding.elim_box"), (FStar_Getopt.OneArg ((((string_as_bool "smtencoding.elim_box")), ("true|false")))), ("Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default \'false\')")))::(((FStar_Getopt.noshort), ("smtencoding.nl_arith_repr"), (FStar_Getopt.OneArg ((((fun _0_44 -> String (_0_44))), ("native|wrapped|boxwrap")))), ("Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if \'boxwrap\' use \'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus\'; \n\t\tif \'native\' use \'*, div, mod\';\n\t\tif \'wrapped\' use \'_mul, _div, _mod : Int*Int -> Int\'; \n\t\t(default \'boxwrap\')")))::(((FStar_Getopt.noshort), ("smtencoding.l_arith_repr"), (FStar_Getopt.OneArg ((((fun _0_45 -> String (_0_45))), ("native|boxwrap")))), ("Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if \'boxwrap\', use \'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus\'; \n\t\tif \'native\', use \'+, -, -\'; \n\t\t(default \'boxwrap\')")))::(((FStar_Getopt.noshort), ("split_cases"), (FStar_Getopt.OneArg ((((fun n1 -> (

let uu____1814 = (FStar_Util.int_of_string n1)
in Int (uu____1814)))), ("[positive integer]")))), ("Partition VC of a match into groups of [n] cases")))::(((FStar_Getopt.noshort), ("timing"), (FStar_Getopt.ZeroArgs ((fun uu____1822 -> Bool (true)))), ("Print the time it takes to verify each top-level definition")))::(((FStar_Getopt.noshort), ("trace_error"), (FStar_Getopt.ZeroArgs ((fun uu____1830 -> Bool (true)))), ("Don\'t print an error message; show an exception trace instead")))::(((FStar_Getopt.noshort), ("ugly"), (FStar_Getopt.ZeroArgs ((fun uu____1838 -> Bool (true)))), ("Emit output formatted for debugging")))::(((FStar_Getopt.noshort), ("unthrottle_inductives"), (FStar_Getopt.ZeroArgs ((fun uu____1846 -> Bool (true)))), ("Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")))::(((FStar_Getopt.noshort), ("use_eq_at_higher_order"), (FStar_Getopt.ZeroArgs ((fun uu____1854 -> Bool (true)))), ("Use equality constraints when comparing higher-order types (Temporary)")))::(((FStar_Getopt.noshort), ("use_hints"), (FStar_Getopt.ZeroArgs ((fun uu____1862 -> Bool (true)))), ("Use a previously recorded hints database for proof replay")))::(((FStar_Getopt.noshort), ("no_tactics"), (FStar_Getopt.ZeroArgs ((fun uu____1870 -> Bool (true)))), ("Do not run the tactic engine before discharging a VC")))::(((FStar_Getopt.noshort), ("using_facts_from"), (FStar_Getopt.OneArg (((cons_using_facts_from), ("[namespace | fact id]")))), ("Implies --z3refresh; prunes the context to include facts from the given namespace of fact id (multiple uses of this option will prune the context to include those facts that match any of the provided namespaces / fact ids")))::(((FStar_Getopt.noshort), ("verify_all"), (FStar_Getopt.ZeroArgs ((fun uu____1886 -> Bool (true)))), ("With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.")))::(((FStar_Getopt.noshort), ("verify_module"), (FStar_Getopt.OneArg (((cons_verify_module), ("[module name]")))), ("Name of the module to verify")))::(((FStar_Getopt.noshort), ("__temp_no_proj"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1906 = (

let uu____1908 = (

let uu____1910 = (get___temp_no_proj ())
in (x)::uu____1910)
in (FStar_All.pipe_right uu____1908 (FStar_List.map (fun _0_46 -> String (_0_46)))))
in List (uu____1906)))), ("[module name]")))), ("Don\'t generate projectors for this module")))::((('v'), ("version"), (FStar_Getopt.ZeroArgs ((fun uu____1922 -> ((display_version ());
(FStar_All.exit (Prims.parse_int "0"));
)))), ("Display version number")))::(((FStar_Getopt.noshort), ("warn_default_effects"), (FStar_Getopt.ZeroArgs ((fun uu____1931 -> Bool (true)))), ("Warn when (a -> b) is desugared to (a -> Tot b)")))::(((FStar_Getopt.noshort), ("z3cliopt"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1943 = (

let uu____1945 = (

let uu____1947 = (get_z3cliopt ())
in (FStar_List.append uu____1947 ((s)::[])))
in (FStar_All.pipe_right uu____1945 (FStar_List.map (fun _0_47 -> String (_0_47)))))
in List (uu____1943)))), ("[option]")))), ("Z3 command line options")))::(((FStar_Getopt.noshort), ("z3refresh"), (FStar_Getopt.ZeroArgs ((fun uu____1958 -> Bool (true)))), ("Restart Z3 after each query; useful for ensuring proof robustness")))::(((FStar_Getopt.noshort), ("z3rlimit"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1970 = (FStar_Util.int_of_string s)
in Int (uu____1970)))), ("[positive integer]")))), ("Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")))::(((FStar_Getopt.noshort), ("z3rlimit_factor"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1982 = (FStar_Util.int_of_string s)
in Int (uu____1982)))), ("[positive integer]")))), ("Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")))::(((FStar_Getopt.noshort), ("z3seed"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1994 = (FStar_Util.int_of_string s)
in Int (uu____1994)))), ("[positive integer]")))), ("Set the Z3 random seed (default 0)")))::(((FStar_Getopt.noshort), ("__no_positivity"), (FStar_Getopt.ZeroArgs ((fun uu____2002 -> Bool (true)))), ("Don\'t check positivity of inductive types")))::[]
in (

let uu____2008 = (FStar_List.map mk_spec specs1)
in ((('h'), ("help"), (FStar_Getopt.ZeroArgs ((fun x -> ((display_usage_aux specs1);
(FStar_All.exit (Prims.parse_int "0"));
)))), ("Display this information")))::uu____2008)))
and parse_codegen : Prims.string  ->  Prims.string = (fun s -> (match (s) with
| "Kremlin" -> begin
s
end
| "OCaml" -> begin
s
end
| "FSharp" -> begin
s
end
| uu____2031 -> begin
((FStar_Util.print_string "Wrong argument to codegen flag\n");
(

let uu____2034 = (specs ())
in (display_usage_aux uu____2034));
(FStar_All.exit (Prims.parse_int "1"));
)
end))
and string_as_bool : Prims.string  ->  Prims.string  ->  option_val = (fun option_name uu___55_2042 -> (match (uu___55_2042) with
| "true" -> begin
Bool (true)
end
| "false" -> begin
Bool (false)
end
| uu____2043 -> begin
((FStar_Util.print1 "Wrong argument to %s\n" option_name);
(

let uu____2046 = (specs ())
in (display_usage_aux uu____2046));
(FStar_All.exit (Prims.parse_int "1"));
)
end))
and validate_dir : Prims.string  ->  Prims.string = (fun p -> ((FStar_Util.mkdir false p);
p;
))


let docs : Prims.unit  ->  (Prims.string * Prims.string) Prims.list = (fun uu____2061 -> (

let uu____2062 = (specs ())
in (FStar_List.map (fun uu____2081 -> (match (uu____2081) with
| (uu____2089, name, uu____2091, doc) -> begin
((name), (doc))
end)) uu____2062)))


let settable : Prims.string  ->  Prims.bool = (fun uu___56_2098 -> (match (uu___56_2098) with
| "admit_smt_queries" -> begin
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
| "inline_arith" -> begin
true
end
| "lax" -> begin
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
| "print_fuels" -> begin
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
| uu____2099 -> begin
false
end))


let resettable : Prims.string  ->  Prims.bool = (fun s -> (((settable s) || (s = "z3seed")) || (s = "z3cliopt")))


let all_specs : FStar_Getopt.opt Prims.list = (specs ())


let settable_specs : (FStar_BaseTypes.char * Prims.string * Prims.unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____2128 -> (match (uu____2128) with
| (uu____2134, x, uu____2136, uu____2137) -> begin
(settable x)
end))))


let resettable_specs : (FStar_BaseTypes.char * Prims.string * Prims.unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____2163 -> (match (uu____2163) with
| (uu____2169, x, uu____2171, uu____2172) -> begin
(resettable x)
end))))


let display_usage : Prims.unit  ->  Prims.unit = (fun uu____2178 -> (

let uu____2179 = (specs ())
in (display_usage_aux uu____2179)))


let fstar_home : Prims.unit  ->  Prims.string = (fun uu____2189 -> (

let uu____2190 = (get_fstar_home ())
in (match (uu____2190) with
| FStar_Pervasives_Native.None -> begin
(

let x = (FStar_Util.get_exec_dir ())
in (

let x1 = (Prims.strcat x "/..")
in ((set_option' (("fstar_home"), (String (x1))));
x1;
)))
end
| FStar_Pervasives_Native.Some (x) -> begin
x
end)))

exception File_argument of (Prims.string)


let uu___is_File_argument : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| File_argument (uu____2203) -> begin
true
end
| uu____2204 -> begin
false
end))


let __proj__File_argument__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| File_argument (uu____2212) -> begin
uu____2212
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
in try
(match (()) with
| () -> begin
(match ((s = "")) with
| true -> begin
FStar_Getopt.Success
end
| uu____2236 -> begin
(FStar_Getopt.parse_string specs1 (fun s1 -> (FStar_Pervasives.raise (File_argument (s1)))) s)
end)
end)
with
| File_argument (s1) -> begin
(

let uu____2246 = (FStar_Util.format1 "File %s is not a valid option" s1)
in FStar_Getopt.Error (uu____2246))
end))


let file_list_ : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let parse_cmd_line : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____2258 -> (

let res = (

let uu____2260 = (specs ())
in (FStar_Getopt.parse_cmdline uu____2260 (fun i -> (

let uu____2265 = (

let uu____2267 = (FStar_ST.read file_list_)
in (FStar_List.append uu____2267 ((i)::[])))
in (FStar_ST.write file_list_ uu____2265)))))
in (

let uu____2275 = (

let uu____2277 = (FStar_ST.read file_list_)
in (FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____2277))
in ((res), (uu____2275)))))


let file_list : Prims.unit  ->  Prims.string Prims.list = (fun uu____2287 -> (FStar_ST.read file_list_))


let restore_cmd_line_options : Prims.bool  ->  FStar_Getopt.parse_cmdline_res = (fun should_clear -> (

let old_verify_module = (get_verify_module ())
in ((match (should_clear) with
| true -> begin
(clear ())
end
| uu____2298 -> begin
(init ())
end);
(

let r = (

let uu____2300 = (specs ())
in (FStar_Getopt.parse_cmdline uu____2300 (fun x -> ())))
in ((

let uu____2305 = (

let uu____2308 = (

let uu____2309 = (FStar_List.map (fun _0_48 -> String (_0_48)) old_verify_module)
in List (uu____2309))
in (("verify_module"), (uu____2308)))
in (set_option' uu____2305));
r;
));
)))


let should_verify : Prims.string  ->  Prims.bool = (fun m -> (

let uu____2315 = (get_lax ())
in (match (uu____2315) with
| true -> begin
false
end
| uu____2316 -> begin
(

let uu____2317 = (get_verify_all ())
in (match (uu____2317) with
| true -> begin
true
end
| uu____2318 -> begin
(

let uu____2319 = (get_verify_module ())
in (match (uu____2319) with
| [] -> begin
(

let uu____2321 = (file_list ())
in (FStar_List.existsML (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let f2 = (

let uu____2329 = (

let uu____2330 = (

let uu____2331 = (

let uu____2332 = (FStar_Util.get_file_extension f1)
in (FStar_String.length uu____2332))
in ((FStar_String.length f1) - uu____2331))
in (uu____2330 - (Prims.parse_int "1")))
in (FStar_String.substring f1 (Prims.parse_int "0") uu____2329))
in ((FStar_String.lowercase f2) = m)))) uu____2321))
end
| l -> begin
(FStar_List.contains (FStar_String.lowercase m) l)
end))
end))
end)))


let dont_gen_projectors : Prims.string  ->  Prims.bool = (fun m -> (

let uu____2347 = (get___temp_no_proj ())
in (FStar_List.contains m uu____2347)))


let should_print_message : Prims.string  ->  Prims.bool = (fun m -> (

let uu____2353 = (should_verify m)
in (match (uu____2353) with
| true -> begin
(m <> "Prims")
end
| uu____2354 -> begin
false
end)))


let include_path : Prims.unit  ->  Prims.string Prims.list = (fun uu____2359 -> (

let uu____2360 = (get_no_default_includes ())
in (match (uu____2360) with
| true -> begin
(get_include ())
end
| uu____2362 -> begin
(

let h = (fstar_home ())
in (

let defs = universe_include_path_base_dirs
in (

let uu____2366 = (

let uu____2368 = (FStar_All.pipe_right defs (FStar_List.map (fun x -> (Prims.strcat h x))))
in (FStar_All.pipe_right uu____2368 (FStar_List.filter FStar_Util.file_exists)))
in (

let uu____2376 = (

let uu____2378 = (get_include ())
in (FStar_List.append uu____2378 ((".")::[])))
in (FStar_List.append uu____2366 uu____2376)))))
end)))


let find_file : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun filename -> (

let uu____2385 = (FStar_Util.is_path_absolute filename)
in (match (uu____2385) with
| true -> begin
(match ((FStar_Util.file_exists filename)) with
| true -> begin
FStar_Pervasives_Native.Some (filename)
end
| uu____2388 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____2389 -> begin
(

let uu____2390 = (

let uu____2392 = (include_path ())
in (FStar_List.rev uu____2392))
in (FStar_Util.find_map uu____2390 (fun p -> (

let path = (FStar_Util.join_paths p filename)
in (match ((FStar_Util.file_exists path)) with
| true -> begin
FStar_Pervasives_Native.Some (path)
end
| uu____2399 -> begin
FStar_Pervasives_Native.None
end)))))
end)))


let prims : Prims.unit  ->  Prims.string = (fun uu____2403 -> (

let uu____2404 = (get_prims ())
in (match (uu____2404) with
| FStar_Pervasives_Native.None -> begin
(

let filename = "prims.fst"
in (

let uu____2407 = (find_file filename)
in (match (uu____2407) with
| FStar_Pervasives_Native.Some (result) -> begin
result
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2410 = (

let uu____2411 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in FStar_Util.Failure (uu____2411))
in (FStar_Pervasives.raise uu____2410))
end)))
end
| FStar_Pervasives_Native.Some (x) -> begin
x
end)))


let prims_basename : Prims.unit  ->  Prims.string = (fun uu____2416 -> (

let uu____2417 = (prims ())
in (FStar_Util.basename uu____2417)))


let pervasives : Prims.unit  ->  Prims.string = (fun uu____2421 -> (

let filename = "FStar.Pervasives.fst"
in (

let uu____2423 = (find_file filename)
in (match (uu____2423) with
| FStar_Pervasives_Native.Some (result) -> begin
result
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2426 = (

let uu____2427 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in FStar_Util.Failure (uu____2427))
in (FStar_Pervasives.raise uu____2426))
end))))


let pervasives_basename : Prims.unit  ->  Prims.string = (fun uu____2431 -> (

let uu____2432 = (pervasives ())
in (FStar_Util.basename uu____2432)))


let pervasives_native_basename : Prims.unit  ->  Prims.string = (fun uu____2436 -> (

let filename = "FStar.Pervasives.Native.fst"
in (

let uu____2438 = (find_file filename)
in (match (uu____2438) with
| FStar_Pervasives_Native.Some (result) -> begin
(FStar_Util.basename result)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2441 = (

let uu____2442 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in FStar_Util.Failure (uu____2442))
in (FStar_Pervasives.raise uu____2441))
end))))


let prepend_output_dir : Prims.string  ->  Prims.string = (fun fname -> (

let uu____2447 = (get_odir ())
in (match (uu____2447) with
| FStar_Pervasives_Native.None -> begin
fname
end
| FStar_Pervasives_Native.Some (x) -> begin
(Prims.strcat x (Prims.strcat "/" fname))
end)))


let __temp_no_proj : Prims.string  ->  Prims.bool = (fun s -> (

let uu____2454 = (get___temp_no_proj ())
in (FStar_All.pipe_right uu____2454 (FStar_List.contains s))))


let admit_smt_queries : Prims.unit  ->  Prims.bool = (fun uu____2460 -> (get_admit_smt_queries ()))


let check_hints : Prims.unit  ->  Prims.bool = (fun uu____2464 -> (get_check_hints ()))


let codegen : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2469 -> (get_codegen ()))


let codegen_libs : Prims.unit  ->  Prims.string Prims.list Prims.list = (fun uu____2475 -> (

let uu____2476 = (get_codegen_lib ())
in (FStar_All.pipe_right uu____2476 (FStar_List.map (fun x -> (FStar_Util.split x "."))))))


let debug_any : Prims.unit  ->  Prims.bool = (fun uu____2487 -> (

let uu____2488 = (get_debug ())
in (uu____2488 <> [])))


let debug_at_level : Prims.string  ->  debug_level_t  ->  Prims.bool = (fun modul level -> (((modul = "") || (

let uu____2500 = (get_debug ())
in (FStar_All.pipe_right uu____2500 (FStar_List.contains modul)))) && (debug_level_geq level)))


let dep : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2507 -> (get_dep ()))


let detail_errors : Prims.unit  ->  Prims.bool = (fun uu____2511 -> (get_detail_errors ()))


let doc : Prims.unit  ->  Prims.bool = (fun uu____2515 -> (get_doc ()))


let dump_module : Prims.string  ->  Prims.bool = (fun s -> (

let uu____2520 = (get_dump_module ())
in (FStar_All.pipe_right uu____2520 (FStar_List.contains s))))


let eager_inference : Prims.unit  ->  Prims.bool = (fun uu____2526 -> (get_eager_inference ()))


let explicit_deps : Prims.unit  ->  Prims.bool = (fun uu____2530 -> (get_explicit_deps ()))


let extract_all : Prims.unit  ->  Prims.bool = (fun uu____2534 -> (get_extract_all ()))


let fs_typ_app : Prims.string  ->  Prims.bool = (fun filename -> (

let uu____2539 = (FStar_ST.read light_off_files)
in (FStar_List.contains filename uu____2539)))


let full_context_dependency : Prims.unit  ->  Prims.bool = (fun uu____2547 -> true)


let hide_genident_nums : Prims.unit  ->  Prims.bool = (fun uu____2551 -> (get_hide_genident_nums ()))


let hide_uvar_nums : Prims.unit  ->  Prims.bool = (fun uu____2555 -> (get_hide_uvar_nums ()))


let hint_info : Prims.unit  ->  Prims.bool = (fun uu____2559 -> (get_hint_info ()))


let hint_file : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2564 -> (get_hint_file ()))


let ide : Prims.unit  ->  Prims.bool = (fun uu____2568 -> (get_ide ()))


let indent : Prims.unit  ->  Prims.bool = (fun uu____2572 -> (get_indent ()))


let initial_fuel : Prims.unit  ->  Prims.int = (fun uu____2576 -> (

let uu____2577 = (get_initial_fuel ())
in (

let uu____2578 = (get_max_fuel ())
in (Prims.min uu____2577 uu____2578))))


let initial_ifuel : Prims.unit  ->  Prims.int = (fun uu____2582 -> (

let uu____2583 = (get_initial_ifuel ())
in (

let uu____2584 = (get_max_ifuel ())
in (Prims.min uu____2583 uu____2584))))


let interactive : Prims.unit  ->  Prims.bool = (fun uu____2588 -> ((get_in ()) || (get_ide ())))


let lax : Prims.unit  ->  Prims.bool = (fun uu____2592 -> (get_lax ()))


let load : Prims.unit  ->  Prims.string Prims.list = (fun uu____2597 -> (get_load ()))


let legacy_interactive : Prims.unit  ->  Prims.bool = (fun uu____2601 -> (get_in ()))


let log_queries : Prims.unit  ->  Prims.bool = (fun uu____2605 -> (get_log_queries ()))


let log_types : Prims.unit  ->  Prims.bool = (fun uu____2609 -> (get_log_types ()))


let max_fuel : Prims.unit  ->  Prims.int = (fun uu____2613 -> (get_max_fuel ()))


let max_ifuel : Prims.unit  ->  Prims.int = (fun uu____2617 -> (get_max_ifuel ()))


let min_fuel : Prims.unit  ->  Prims.int = (fun uu____2621 -> (get_min_fuel ()))


let ml_ish : Prims.unit  ->  Prims.bool = (fun uu____2625 -> (get_MLish ()))


let set_ml_ish : Prims.unit  ->  Prims.unit = (fun uu____2629 -> (set_option "MLish" (Bool (true))))


let n_cores : Prims.unit  ->  Prims.int = (fun uu____2633 -> (get_n_cores ()))


let no_default_includes : Prims.unit  ->  Prims.bool = (fun uu____2637 -> (get_no_default_includes ()))


let no_extract : Prims.string  ->  Prims.bool = (fun s -> (

let uu____2642 = (get_no_extract ())
in (FStar_All.pipe_right uu____2642 (FStar_List.contains s))))


let no_location_info : Prims.unit  ->  Prims.bool = (fun uu____2648 -> (get_no_location_info ()))


let output_dir : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2653 -> (get_odir ()))


let ugly : Prims.unit  ->  Prims.bool = (fun uu____2657 -> (get_ugly ()))


let print_bound_var_types : Prims.unit  ->  Prims.bool = (fun uu____2661 -> (get_print_bound_var_types ()))


let print_effect_args : Prims.unit  ->  Prims.bool = (fun uu____2665 -> (get_print_effect_args ()))


let print_fuels : Prims.unit  ->  Prims.bool = (fun uu____2669 -> (get_print_fuels ()))


let print_implicits : Prims.unit  ->  Prims.bool = (fun uu____2673 -> (get_print_implicits ()))


let print_real_names : Prims.unit  ->  Prims.bool = (fun uu____2677 -> ((get_prn ()) || (get_print_full_names ())))


let print_universes : Prims.unit  ->  Prims.bool = (fun uu____2681 -> (get_print_universes ()))


let print_z3_statistics : Prims.unit  ->  Prims.bool = (fun uu____2685 -> (get_print_z3_statistics ()))


let record_hints : Prims.unit  ->  Prims.bool = (fun uu____2689 -> (get_record_hints ()))


let reuse_hint_for : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____2694 -> (get_reuse_hint_for ()))


let silent : Prims.unit  ->  Prims.bool = (fun uu____2698 -> (get_silent ()))


let smtencoding_elim_box : Prims.unit  ->  Prims.bool = (fun uu____2702 -> (get_smtencoding_elim_box ()))


let smtencoding_nl_arith_native : Prims.unit  ->  Prims.bool = (fun uu____2706 -> (

let uu____2707 = (get_smtencoding_nl_arith_repr ())
in (uu____2707 = "native")))


let smtencoding_nl_arith_wrapped : Prims.unit  ->  Prims.bool = (fun uu____2711 -> (

let uu____2712 = (get_smtencoding_nl_arith_repr ())
in (uu____2712 = "wrapped")))


let smtencoding_nl_arith_default : Prims.unit  ->  Prims.bool = (fun uu____2716 -> (

let uu____2717 = (get_smtencoding_nl_arith_repr ())
in (uu____2717 = "boxwrap")))


let smtencoding_l_arith_native : Prims.unit  ->  Prims.bool = (fun uu____2721 -> (

let uu____2722 = (get_smtencoding_l_arith_repr ())
in (uu____2722 = "native")))


let smtencoding_l_arith_default : Prims.unit  ->  Prims.bool = (fun uu____2726 -> (

let uu____2727 = (get_smtencoding_l_arith_repr ())
in (uu____2727 = "boxwrap")))


let split_cases : Prims.unit  ->  Prims.int = (fun uu____2731 -> (get_split_cases ()))


let timing : Prims.unit  ->  Prims.bool = (fun uu____2735 -> (get_timing ()))


let trace_error : Prims.unit  ->  Prims.bool = (fun uu____2739 -> (get_trace_error ()))


let unthrottle_inductives : Prims.unit  ->  Prims.bool = (fun uu____2743 -> (get_unthrottle_inductives ()))


let use_eq_at_higher_order : Prims.unit  ->  Prims.bool = (fun uu____2747 -> (get_use_eq_at_higher_order ()))


let use_hints : Prims.unit  ->  Prims.bool = (fun uu____2751 -> (get_use_hints ()))


let use_tactics : Prims.unit  ->  Prims.bool = (fun uu____2755 -> (get_use_tactics ()))


let using_facts_from : Prims.unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____2761 -> (get_using_facts_from ()))


let verify_all : Prims.unit  ->  Prims.bool = (fun uu____2765 -> (get_verify_all ()))


let verify_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____2770 -> (get_verify_module ()))


let warn_default_effects : Prims.unit  ->  Prims.bool = (fun uu____2774 -> (get_warn_default_effects ()))


let z3_exe : Prims.unit  ->  Prims.string = (fun uu____2778 -> (

let uu____2779 = (get_smt ())
in (match (uu____2779) with
| FStar_Pervasives_Native.None -> begin
(FStar_Platform.exe "z3")
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let z3_cliopt : Prims.unit  ->  Prims.string Prims.list = (fun uu____2786 -> (get_z3cliopt ()))


let z3_refresh : Prims.unit  ->  Prims.bool = (fun uu____2790 -> (get_z3refresh ()))


let z3_rlimit : Prims.unit  ->  Prims.int = (fun uu____2794 -> (get_z3rlimit ()))


let z3_rlimit_factor : Prims.unit  ->  Prims.int = (fun uu____2798 -> (get_z3rlimit_factor ()))


let z3_seed : Prims.unit  ->  Prims.int = (fun uu____2802 -> (get_z3seed ()))


let no_positivity : Prims.unit  ->  Prims.bool = (fun uu____2806 -> (get_no_positivity ()))


let should_extract : Prims.string  ->  Prims.bool = (fun m -> ((

let uu____2813 = (no_extract m)
in (not (uu____2813))) && ((extract_all ()) || (

let uu____2816 = (get_extract_module ())
in (match (uu____2816) with
| [] -> begin
(

let uu____2818 = (get_extract_namespace ())
in (match (uu____2818) with
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




