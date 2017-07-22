
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

type options =
| Set
| Reset
| Restore


let uu___is_Set : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Set -> begin
true
end
| uu____148 -> begin
false
end))


let uu___is_Reset : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reset -> begin
true
end
| uu____153 -> begin
false
end))


let uu___is_Restore : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Restore -> begin
true
end
| uu____158 -> begin
false
end))


let __unit_tests__ : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let __unit_tests : Prims.unit  ->  Prims.bool = (fun uu____165 -> (FStar_ST.read __unit_tests__))


let __set_unit_tests : Prims.unit  ->  Prims.unit = (fun uu____169 -> (FStar_ST.write __unit_tests__ true))


let __clear_unit_tests : Prims.unit  ->  Prims.unit = (fun uu____173 -> (FStar_ST.write __unit_tests__ false))


let as_bool : option_val  ->  Prims.bool = (fun uu___49_177 -> (match (uu___49_177) with
| Bool (b) -> begin
b
end
| uu____179 -> begin
(failwith "Impos: expected Bool")
end))


let as_int : option_val  ->  Prims.int = (fun uu___50_183 -> (match (uu___50_183) with
| Int (b) -> begin
b
end
| uu____185 -> begin
(failwith "Impos: expected Int")
end))


let as_string : option_val  ->  Prims.string = (fun uu___51_189 -> (match (uu___51_189) with
| String (b) -> begin
b
end
| Path (b) -> begin
(FStar_Common.try_convert_file_name_to_mixed b)
end
| uu____192 -> begin
(failwith "Impos: expected String")
end))


let as_list : 'Auu____199 . (option_val  ->  'Auu____199)  ->  option_val  ->  'Auu____199 Prims.list = (fun as_t uu___52_212 -> (match (uu___52_212) with
| List (ts) -> begin
(FStar_All.pipe_right ts (FStar_List.map as_t))
end
| uu____222 -> begin
(failwith "Impos: expected List")
end))


let as_option : 'Auu____231 . (option_val  ->  'Auu____231)  ->  option_val  ->  'Auu____231 FStar_Pervasives_Native.option = (fun as_t uu___53_244 -> (match (uu___53_244) with
| Unset -> begin
FStar_Pervasives_Native.None
end
| v1 -> begin
(

let uu____248 = (as_t v1)
in FStar_Pervasives_Native.Some (uu____248))
end))


type optionstate =
option_val FStar_Util.smap


let fstar_options : optionstate Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let peek : Prims.unit  ->  optionstate = (fun uu____261 -> (

let uu____262 = (FStar_ST.read fstar_options)
in (FStar_List.hd uu____262)))


let pop : Prims.unit  ->  Prims.unit = (fun uu____270 -> (

let uu____271 = (FStar_ST.read fstar_options)
in (match (uu____271) with
| [] -> begin
(failwith "TOO MANY POPS!")
end
| (uu____276)::[] -> begin
(failwith "TOO MANY POPS!")
end
| (uu____277)::tl1 -> begin
(FStar_ST.write fstar_options tl1)
end)))


let push : Prims.unit  ->  Prims.unit = (fun uu____286 -> (

let uu____287 = (

let uu____290 = (

let uu____293 = (peek ())
in (FStar_Util.smap_copy uu____293))
in (

let uu____296 = (FStar_ST.read fstar_options)
in (uu____290)::uu____296))
in (FStar_ST.write fstar_options uu____287)))


let set : optionstate  ->  Prims.unit = (fun o -> (

let uu____311 = (FStar_ST.read fstar_options)
in (match (uu____311) with
| [] -> begin
(failwith "set on empty option stack")
end
| (uu____316)::os -> begin
(FStar_ST.write fstar_options ((o)::os))
end)))


let set_option : Prims.string  ->  option_val  ->  Prims.unit = (fun k v1 -> (

let uu____330 = (peek ())
in (FStar_Util.smap_add uu____330 k v1)))


let set_option' : (Prims.string * option_val)  ->  Prims.unit = (fun uu____340 -> (match (uu____340) with
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

let uu____375 = (

let uu____378 = (FStar_ST.read light_off_files)
in (filename)::uu____378)
in (FStar_ST.write light_off_files uu____375)))


let defaults : (Prims.string * option_val) Prims.list = ((("__temp_no_proj"), (List ([]))))::((("_fstar_home"), (String (""))))::((("_include_path"), (List ([]))))::((("admit_smt_queries"), (Bool (false))))::((("admit_except"), (Unset)))::((("check_hints"), (Bool (false))))::((("codegen"), (Unset)))::((("codegen-lib"), (List ([]))))::((("debug"), (List ([]))))::((("debug_level"), (List ([]))))::((("dep"), (Unset)))::((("detail_errors"), (Bool (false))))::((("detail_hint_replay"), (Bool (false))))::((("doc"), (Bool (false))))::((("dump_module"), (List ([]))))::((("eager_inference"), (Bool (false))))::((("explicit_deps"), (Bool (false))))::((("extract_all"), (Bool (false))))::((("extract_module"), (List ([]))))::((("extract_namespace"), (List ([]))))::((("fs_typ_app"), (Bool (false))))::((("fstar_home"), (Unset)))::((("full_context_dependency"), (Bool (true))))::((("hide_genident_nums"), (Bool (false))))::((("hide_uvar_nums"), (Bool (false))))::((("hint_info"), (Bool (false))))::((("hint_file"), (Unset)))::((("in"), (Bool (false))))::((("ide"), (Bool (false))))::((("include"), (List ([]))))::((("indent"), (Bool (false))))::((("initial_fuel"), (Int ((Prims.parse_int "2")))))::((("initial_ifuel"), (Int ((Prims.parse_int "1")))))::((("lax"), (Bool (false))))::((("load"), (List ([]))))::((("log_queries"), (Bool (false))))::((("log_types"), (Bool (false))))::((("max_fuel"), (Int ((Prims.parse_int "8")))))::((("max_ifuel"), (Int ((Prims.parse_int "2")))))::((("min_fuel"), (Int ((Prims.parse_int "1")))))::((("MLish"), (Bool (false))))::((("n_cores"), (Int ((Prims.parse_int "1")))))::((("no_default_includes"), (Bool (false))))::((("no_extract"), (List ([]))))::((("no_location_info"), (Bool (false))))::((("odir"), (Unset)))::((("prims"), (Unset)))::((("pretype"), (Bool (true))))::((("prims_ref"), (Unset)))::((("print_bound_var_types"), (Bool (false))))::((("print_effect_args"), (Bool (false))))::((("print_fuels"), (Bool (false))))::((("print_full_names"), (Bool (false))))::((("print_implicits"), (Bool (false))))::((("print_universes"), (Bool (false))))::((("print_z3_statistics"), (Bool (false))))::((("prn"), (Bool (false))))::((("record_hints"), (Bool (false))))::((("reuse_hint_for"), (Unset)))::((("show_signatures"), (List ([]))))::((("silent"), (Bool (false))))::((("smt"), (Unset)))::((("smtencoding.elim_box"), (Bool (false))))::((("smtencoding.nl_arith_repr"), (String ("boxwrap"))))::((("smtencoding.l_arith_repr"), (String ("boxwrap"))))::((("split_cases"), (Int ((Prims.parse_int "0")))))::((("timing"), (Bool (false))))::((("trace_error"), (Bool (false))))::((("ugly"), (Bool (false))))::((("unthrottle_inductives"), (Bool (false))))::((("use_eq_at_higher_order"), (Bool (false))))::((("use_hints"), (Bool (false))))::((("no_tactics"), (Bool (false))))::((("using_facts_from"), (Unset)))::((("verify"), (Bool (true))))::((("verify_all"), (Bool (false))))::((("verify_module"), (List ([]))))::((("warn_default_effects"), (Bool (false))))::((("z3refresh"), (Bool (false))))::((("z3rlimit"), (Int ((Prims.parse_int "5")))))::((("z3rlimit_factor"), (Int ((Prims.parse_int "1")))))::((("z3seed"), (Int ((Prims.parse_int "0")))))::((("z3cliopt"), (List ([]))))::((("__no_positivity"), (Bool (false))))::((("__ml_no_eta_expand_coertions"), (Bool (false))))::[]


let init : Prims.unit  ->  Prims.unit = (fun uu____738 -> (

let o = (peek ())
in ((FStar_Util.smap_clear o);
(FStar_All.pipe_right defaults (FStar_List.iter set_option'));
)))


let clear : Prims.unit  ->  Prims.unit = (fun uu____754 -> (

let o = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_ST.write fstar_options ((o)::[]));
(FStar_ST.write light_off_files []);
(init ());
)))


let _run : Prims.unit = (clear ())


let get_option : Prims.string  ->  option_val = (fun s -> (

let uu____772 = (

let uu____775 = (peek ())
in (FStar_Util.smap_try_find uu____775 s))
in (match (uu____772) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Impossible: option " (Prims.strcat s " not found")))
end
| FStar_Pervasives_Native.Some (s1) -> begin
s1
end)))


let lookup_opt : 'Auu____785 . Prims.string  ->  (option_val  ->  'Auu____785)  ->  'Auu____785 = (fun s c -> (c (get_option s)))


let get_admit_smt_queries : Prims.unit  ->  Prims.bool = (fun uu____802 -> (lookup_opt "admit_smt_queries" as_bool))


let get_admit_except : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____808 -> (lookup_opt "admit_except" (as_option as_string)))


let get_check_hints : Prims.unit  ->  Prims.bool = (fun uu____814 -> (lookup_opt "check_hints" as_bool))


let get_codegen : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____820 -> (lookup_opt "codegen" (as_option as_string)))


let get_codegen_lib : Prims.unit  ->  Prims.string Prims.list = (fun uu____828 -> (lookup_opt "codegen-lib" (as_list as_string)))


let get_debug : Prims.unit  ->  Prims.string Prims.list = (fun uu____836 -> (lookup_opt "debug" (as_list as_string)))


let get_debug_level : Prims.unit  ->  Prims.string Prims.list = (fun uu____844 -> (lookup_opt "debug_level" (as_list as_string)))


let get_dep : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____852 -> (lookup_opt "dep" (as_option as_string)))


let get_detail_errors : Prims.unit  ->  Prims.bool = (fun uu____858 -> (lookup_opt "detail_errors" as_bool))


let get_detail_hint_replay : Prims.unit  ->  Prims.bool = (fun uu____862 -> (lookup_opt "detail_hint_replay" as_bool))


let get_doc : Prims.unit  ->  Prims.bool = (fun uu____866 -> (lookup_opt "doc" as_bool))


let get_dump_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____872 -> (lookup_opt "dump_module" (as_list as_string)))


let get_eager_inference : Prims.unit  ->  Prims.bool = (fun uu____878 -> (lookup_opt "eager_inference" as_bool))


let get_explicit_deps : Prims.unit  ->  Prims.bool = (fun uu____882 -> (lookup_opt "explicit_deps" as_bool))


let get_extract_all : Prims.unit  ->  Prims.bool = (fun uu____886 -> (lookup_opt "extract_all" as_bool))


let get_extract_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____892 -> (lookup_opt "extract_module" (as_list as_string)))


let get_extract_namespace : Prims.unit  ->  Prims.string Prims.list = (fun uu____900 -> (lookup_opt "extract_namespace" (as_list as_string)))


let get_fs_typ_app : Prims.unit  ->  Prims.bool = (fun uu____906 -> (lookup_opt "fs_typ_app" as_bool))


let get_fstar_home : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____912 -> (lookup_opt "fstar_home" (as_option as_string)))


let get_hide_genident_nums : Prims.unit  ->  Prims.bool = (fun uu____918 -> (lookup_opt "hide_genident_nums" as_bool))


let get_hide_uvar_nums : Prims.unit  ->  Prims.bool = (fun uu____922 -> (lookup_opt "hide_uvar_nums" as_bool))


let get_hint_info : Prims.unit  ->  Prims.bool = (fun uu____926 -> (lookup_opt "hint_info" as_bool))


let get_hint_file : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____932 -> (lookup_opt "hint_file" (as_option as_string)))


let get_in : Prims.unit  ->  Prims.bool = (fun uu____938 -> (lookup_opt "in" as_bool))


let get_ide : Prims.unit  ->  Prims.bool = (fun uu____942 -> (lookup_opt "ide" as_bool))


let get_include : Prims.unit  ->  Prims.string Prims.list = (fun uu____948 -> (lookup_opt "include" (as_list as_string)))


let get_indent : Prims.unit  ->  Prims.bool = (fun uu____954 -> (lookup_opt "indent" as_bool))


let get_initial_fuel : Prims.unit  ->  Prims.int = (fun uu____958 -> (lookup_opt "initial_fuel" as_int))


let get_initial_ifuel : Prims.unit  ->  Prims.int = (fun uu____962 -> (lookup_opt "initial_ifuel" as_int))


let get_lax : Prims.unit  ->  Prims.bool = (fun uu____966 -> (lookup_opt "lax" as_bool))


let get_load : Prims.unit  ->  Prims.string Prims.list = (fun uu____972 -> (lookup_opt "load" (as_list as_string)))


let get_log_queries : Prims.unit  ->  Prims.bool = (fun uu____978 -> (lookup_opt "log_queries" as_bool))


let get_log_types : Prims.unit  ->  Prims.bool = (fun uu____982 -> (lookup_opt "log_types" as_bool))


let get_max_fuel : Prims.unit  ->  Prims.int = (fun uu____986 -> (lookup_opt "max_fuel" as_int))


let get_max_ifuel : Prims.unit  ->  Prims.int = (fun uu____990 -> (lookup_opt "max_ifuel" as_int))


let get_min_fuel : Prims.unit  ->  Prims.int = (fun uu____994 -> (lookup_opt "min_fuel" as_int))


let get_MLish : Prims.unit  ->  Prims.bool = (fun uu____998 -> (lookup_opt "MLish" as_bool))


let get_n_cores : Prims.unit  ->  Prims.int = (fun uu____1002 -> (lookup_opt "n_cores" as_int))


let get_no_default_includes : Prims.unit  ->  Prims.bool = (fun uu____1006 -> (lookup_opt "no_default_includes" as_bool))


let get_no_extract : Prims.unit  ->  Prims.string Prims.list = (fun uu____1012 -> (lookup_opt "no_extract" (as_list as_string)))


let get_no_location_info : Prims.unit  ->  Prims.bool = (fun uu____1018 -> (lookup_opt "no_location_info" as_bool))


let get_odir : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1024 -> (lookup_opt "odir" (as_option as_string)))


let get_ugly : Prims.unit  ->  Prims.bool = (fun uu____1030 -> (lookup_opt "ugly" as_bool))


let get_prims : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1036 -> (lookup_opt "prims" (as_option as_string)))


let get_print_bound_var_types : Prims.unit  ->  Prims.bool = (fun uu____1042 -> (lookup_opt "print_bound_var_types" as_bool))


let get_print_effect_args : Prims.unit  ->  Prims.bool = (fun uu____1046 -> (lookup_opt "print_effect_args" as_bool))


let get_print_fuels : Prims.unit  ->  Prims.bool = (fun uu____1050 -> (lookup_opt "print_fuels" as_bool))


let get_print_full_names : Prims.unit  ->  Prims.bool = (fun uu____1054 -> (lookup_opt "print_full_names" as_bool))


let get_print_implicits : Prims.unit  ->  Prims.bool = (fun uu____1058 -> (lookup_opt "print_implicits" as_bool))


let get_print_universes : Prims.unit  ->  Prims.bool = (fun uu____1062 -> (lookup_opt "print_universes" as_bool))


let get_print_z3_statistics : Prims.unit  ->  Prims.bool = (fun uu____1066 -> (lookup_opt "print_z3_statistics" as_bool))


let get_prn : Prims.unit  ->  Prims.bool = (fun uu____1070 -> (lookup_opt "prn" as_bool))


let get_record_hints : Prims.unit  ->  Prims.bool = (fun uu____1074 -> (lookup_opt "record_hints" as_bool))


let get_reuse_hint_for : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1080 -> (lookup_opt "reuse_hint_for" (as_option as_string)))


let get_show_signatures : Prims.unit  ->  Prims.string Prims.list = (fun uu____1088 -> (lookup_opt "show_signatures" (as_list as_string)))


let get_silent : Prims.unit  ->  Prims.bool = (fun uu____1094 -> (lookup_opt "silent" as_bool))


let get_smt : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____1100 -> (lookup_opt "smt" (as_option as_string)))


let get_smtencoding_elim_box : Prims.unit  ->  Prims.bool = (fun uu____1106 -> (lookup_opt "smtencoding.elim_box" as_bool))


let get_smtencoding_nl_arith_repr : Prims.unit  ->  Prims.string = (fun uu____1110 -> (lookup_opt "smtencoding.nl_arith_repr" as_string))


let get_smtencoding_l_arith_repr : Prims.unit  ->  Prims.string = (fun uu____1114 -> (lookup_opt "smtencoding.l_arith_repr" as_string))


let get_split_cases : Prims.unit  ->  Prims.int = (fun uu____1118 -> (lookup_opt "split_cases" as_int))


let get_timing : Prims.unit  ->  Prims.bool = (fun uu____1122 -> (lookup_opt "timing" as_bool))


let get_trace_error : Prims.unit  ->  Prims.bool = (fun uu____1126 -> (lookup_opt "trace_error" as_bool))


let get_unthrottle_inductives : Prims.unit  ->  Prims.bool = (fun uu____1130 -> (lookup_opt "unthrottle_inductives" as_bool))


let get_use_eq_at_higher_order : Prims.unit  ->  Prims.bool = (fun uu____1134 -> (lookup_opt "use_eq_at_higher_order" as_bool))


let get_use_hints : Prims.unit  ->  Prims.bool = (fun uu____1138 -> (lookup_opt "use_hints" as_bool))


let get_use_tactics : Prims.unit  ->  Prims.bool = (fun uu____1142 -> (

let uu____1143 = (lookup_opt "no_tactics" as_bool)
in (not (uu____1143))))


let get_using_facts_from : Prims.unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____1151 -> (lookup_opt "using_facts_from" (as_option (as_list as_string))))


let get_verify_all : Prims.unit  ->  Prims.bool = (fun uu____1161 -> (lookup_opt "verify_all" as_bool))


let get_verify_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____1167 -> (lookup_opt "verify_module" (as_list as_string)))


let get___temp_no_proj : Prims.unit  ->  Prims.string Prims.list = (fun uu____1175 -> (lookup_opt "__temp_no_proj" (as_list as_string)))


let get_version : Prims.unit  ->  Prims.bool = (fun uu____1181 -> (lookup_opt "version" as_bool))


let get_warn_default_effects : Prims.unit  ->  Prims.bool = (fun uu____1185 -> (lookup_opt "warn_default_effects" as_bool))


let get_z3cliopt : Prims.unit  ->  Prims.string Prims.list = (fun uu____1191 -> (lookup_opt "z3cliopt" (as_list as_string)))


let get_z3refresh : Prims.unit  ->  Prims.bool = (fun uu____1197 -> (lookup_opt "z3refresh" as_bool))


let get_z3rlimit : Prims.unit  ->  Prims.int = (fun uu____1201 -> (lookup_opt "z3rlimit" as_int))


let get_z3rlimit_factor : Prims.unit  ->  Prims.int = (fun uu____1205 -> (lookup_opt "z3rlimit_factor" as_int))


let get_z3seed : Prims.unit  ->  Prims.int = (fun uu____1209 -> (lookup_opt "z3seed" as_int))


let get_no_positivity : Prims.unit  ->  Prims.bool = (fun uu____1213 -> (lookup_opt "__no_positivity" as_bool))


let get_ml_no_eta_expand_coertions : Prims.unit  ->  Prims.bool = (fun uu____1217 -> (lookup_opt "__ml_no_eta_expand_coertions" as_bool))


let dlevel : Prims.string  ->  debug_level_t = (fun uu___54_1221 -> (match (uu___54_1221) with
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
| Other (uu____1231) -> begin
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

let uu____1236 = (get_debug_level ())
in (FStar_All.pipe_right uu____1236 (FStar_Util.for_some (fun l1 -> (one_debug_level_geq (dlevel l1) l2))))))


let universe_include_path_base_dirs : Prims.string Prims.list = ("/ulib")::("/lib/fstar")::[]


let _version : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _platform : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _compiler : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _date : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _commit : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let display_version : Prims.unit  ->  Prims.unit = (fun uu____1268 -> (

let uu____1269 = (

let uu____1270 = (FStar_ST.read _version)
in (

let uu____1271 = (FStar_ST.read _platform)
in (

let uu____1272 = (FStar_ST.read _compiler)
in (

let uu____1273 = (FStar_ST.read _date)
in (

let uu____1274 = (FStar_ST.read _commit)
in (FStar_Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1270 uu____1271 uu____1272 uu____1273 uu____1274))))))
in (FStar_Util.print_string uu____1269)))


let display_usage_aux : 'Auu____1281 'Auu____1282 . ('Auu____1282 * Prims.string * 'Auu____1281 FStar_Getopt.opt_variant * Prims.string) Prims.list  ->  Prims.unit = (fun specs -> ((FStar_Util.print_string "fstar.exe [options] file[s]\n");
(FStar_List.iter (fun uu____1329 -> (match (uu____1329) with
| (uu____1340, flag, p, doc) -> begin
(match (p) with
| FStar_Getopt.ZeroArgs (ig) -> begin
(match ((doc = "")) with
| true -> begin
(

let uu____1351 = (

let uu____1352 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format1 "  --%s\n" uu____1352))
in (FStar_Util.print_string uu____1351))
end
| uu____1353 -> begin
(

let uu____1354 = (

let uu____1355 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format2 "  --%s  %s\n" uu____1355 doc))
in (FStar_Util.print_string uu____1354))
end)
end
| FStar_Getopt.OneArg (uu____1356, argname) -> begin
(match ((doc = "")) with
| true -> begin
(

let uu____1362 = (

let uu____1363 = (FStar_Util.colorize_bold flag)
in (

let uu____1364 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format2 "  --%s %s\n" uu____1363 uu____1364)))
in (FStar_Util.print_string uu____1362))
end
| uu____1365 -> begin
(

let uu____1366 = (

let uu____1367 = (FStar_Util.colorize_bold flag)
in (

let uu____1368 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format3 "  --%s %s  %s\n" uu____1367 uu____1368 doc)))
in (FStar_Util.print_string uu____1366))
end)
end)
end)) specs);
))


let mk_spec : (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant * Prims.string)  ->  FStar_Getopt.opt = (fun o -> (

let uu____1393 = o
in (match (uu____1393) with
| (ns, name, arg, desc) -> begin
(

let arg1 = (match (arg) with
| FStar_Getopt.ZeroArgs (f) -> begin
(

let g = (fun uu____1423 -> (

let uu____1424 = (

let uu____1429 = (f ())
in ((name), (uu____1429)))
in (set_option' uu____1424)))
in FStar_Getopt.ZeroArgs (g))
end
| FStar_Getopt.OneArg (f, d) -> begin
(

let g = (fun x -> (

let uu____1440 = (

let uu____1445 = (f x)
in ((name), (uu____1445)))
in (set_option' uu____1440)))
in FStar_Getopt.OneArg (((g), (d))))
end)
in ((ns), (name), (arg1), (desc)))
end)))


let cons_extract_module : Prims.string  ->  option_val = (fun s -> (

let uu____1454 = (

let uu____1457 = (

let uu____1460 = (get_extract_module ())
in ((FStar_String.lowercase s))::uu____1460)
in (FStar_All.pipe_right uu____1457 (FStar_List.map (fun _0_26 -> String (_0_26)))))
in List (uu____1454)))


let cons_extract_namespace : Prims.string  ->  option_val = (fun s -> (

let uu____1471 = (

let uu____1474 = (

let uu____1477 = (get_extract_namespace ())
in ((FStar_String.lowercase s))::uu____1477)
in (FStar_All.pipe_right uu____1474 (FStar_List.map (fun _0_27 -> String (_0_27)))))
in List (uu____1471)))


let add_extract_module : Prims.string  ->  Prims.unit = (fun s -> (

let uu____1488 = (cons_extract_module s)
in (set_option "extract_module" uu____1488)))


let add_extract_namespace : Prims.string  ->  Prims.unit = (fun s -> (

let uu____1493 = (cons_extract_namespace s)
in (set_option "extract_namespace" uu____1493)))


let cons_verify_module : Prims.string  ->  option_val = (fun s -> (

let uu____1498 = (

let uu____1501 = (

let uu____1504 = (get_verify_module ())
in ((FStar_String.lowercase s))::uu____1504)
in (FStar_All.pipe_right uu____1501 (FStar_List.map (fun _0_28 -> String (_0_28)))))
in List (uu____1498)))


let cons_using_facts_from : Prims.string  ->  option_val = (fun s -> ((set_option "z3refresh" (Bool (true)));
(

let uu____1516 = (get_using_facts_from ())
in (match (uu____1516) with
| FStar_Pervasives_Native.None -> begin
List ((String (s))::[])
end
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____1528 = (FStar_List.map (fun _0_29 -> String (_0_29)) ((s)::l))
in List (uu____1528))
end));
))


let add_verify_module : Prims.string  ->  Prims.unit = (fun s -> (

let uu____1535 = (cons_verify_module s)
in (set_option "verify_module" uu____1535)))


let rec specs : Prims.unit  ->  FStar_Getopt.opt Prims.list = (fun uu____1548 -> (

let specs1 = (((FStar_Getopt.noshort), ("admit_smt_queries"), (FStar_Getopt.OneArg ((((fun s -> (match ((s = "true")) with
| true -> begin
Bool (true)
end
| uu____1580 -> begin
(match ((s = "false")) with
| true -> begin
Bool (false)
end
| uu____1581 -> begin
(failwith "Invalid argument to --admit_smt_queries")
end)
end))), ("[true|false]")))), ("Admit SMT queries, unsafe! (default \'false\')")))::(((FStar_Getopt.noshort), ("admit_except"), (FStar_Getopt.OneArg ((((fun _0_30 -> String (_0_30))), ("[id]")))), ("Admit all verification conditions, except those with query label <id> (eg, --admit_except \'(FStar.Fin.pigeonhole, 1)\'")))::(((FStar_Getopt.noshort), ("codegen"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1613 = (parse_codegen s)
in String (uu____1613)))), ("[OCaml|FSharp|Kremlin]")))), ("Generate code for execution")))::(((FStar_Getopt.noshort), ("codegen-lib"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1631 = (

let uu____1634 = (

let uu____1637 = (get_codegen_lib ())
in (s)::uu____1637)
in (FStar_All.pipe_right uu____1634 (FStar_List.map (fun _0_31 -> String (_0_31)))))
in List (uu____1631)))), ("[namespace]")))), ("External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")))::(((FStar_Getopt.noshort), ("debug"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1661 = (

let uu____1664 = (

let uu____1667 = (get_debug ())
in (x)::uu____1667)
in (FStar_All.pipe_right uu____1664 (FStar_List.map (fun _0_32 -> String (_0_32)))))
in List (uu____1661)))), ("[module name]")))), ("Print lots of debugging information while checking module")))::(((FStar_Getopt.noshort), ("debug_level"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1691 = (

let uu____1694 = (

let uu____1697 = (get_debug_level ())
in (x)::uu____1697)
in (FStar_All.pipe_right uu____1694 (FStar_List.map (fun _0_33 -> String (_0_33)))))
in List (uu____1691)))), ("[Low|Medium|High|Extreme|...]")))), ("Control the verbosity of debugging info")))::(((FStar_Getopt.noshort), ("dep"), (FStar_Getopt.OneArg ((((fun x -> (match (((x = "make") || (x = "graph"))) with
| true -> begin
String (x)
end
| uu____1720 -> begin
(failwith "invalid argument to \'dep\'")
end))), ("[make|graph]")))), ("Output the transitive closure of the dependency graph in a format suitable for the given tool")))::(((FStar_Getopt.noshort), ("detail_errors"), (FStar_Getopt.ZeroArgs ((fun uu____1734 -> Bool (true)))), ("Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")))::(((FStar_Getopt.noshort), ("detail_hint_replay"), (FStar_Getopt.ZeroArgs ((fun uu____1748 -> Bool (true)))), ("Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")))::(((FStar_Getopt.noshort), ("doc"), (FStar_Getopt.ZeroArgs ((fun uu____1762 -> Bool (true)))), ("Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")))::(((FStar_Getopt.noshort), ("dump_module"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1780 = (

let uu____1783 = (

let uu____1786 = (get_dump_module ())
in (x)::uu____1786)
in (FStar_All.pipe_right uu____1783 (FStar_List.map (fun _0_34 -> String (_0_34)))))
in (FStar_All.pipe_right uu____1780 (fun _0_35 -> List (_0_35)))))), ("[module name]")))), ("")))::(((FStar_Getopt.noshort), ("eager_inference"), (FStar_Getopt.ZeroArgs ((fun uu____1808 -> Bool (true)))), ("Solve all type-inference constraints eagerly; more efficient but at the cost of generality")))::(((FStar_Getopt.noshort), ("explicit_deps"), (FStar_Getopt.ZeroArgs ((fun uu____1822 -> Bool (true)))), ("Do not find dependencies automatically, the user provides them on the command-line")))::(((FStar_Getopt.noshort), ("extract_all"), (FStar_Getopt.ZeroArgs ((fun uu____1836 -> Bool (true)))), ("Discover the complete dependency graph and do not stop at interface boundaries")))::(((FStar_Getopt.noshort), ("extract_module"), (FStar_Getopt.OneArg (((cons_extract_module), ("[module name]")))), ("Only extract the specified modules (instead of the possibly-partial dependency graph)")))::(((FStar_Getopt.noshort), ("extract_namespace"), (FStar_Getopt.OneArg (((cons_extract_namespace), ("[namespace name]")))), ("Only extract modules in the specified namespace")))::(((FStar_Getopt.noshort), ("fstar_home"), (FStar_Getopt.OneArg ((((fun _0_36 -> Path (_0_36))), ("[dir]")))), ("Set the FSTAR_HOME variable to [dir]")))::(((FStar_Getopt.noshort), ("hide_genident_nums"), (FStar_Getopt.ZeroArgs ((fun uu____1892 -> Bool (true)))), ("Don\'t print generated identifier numbers")))::(((FStar_Getopt.noshort), ("hide_uvar_nums"), (FStar_Getopt.ZeroArgs ((fun uu____1906 -> Bool (true)))), ("Don\'t print unification variable numbers")))::(((FStar_Getopt.noshort), ("hint_info"), (FStar_Getopt.ZeroArgs ((fun uu____1920 -> Bool (true)))), ("Print information regarding hints")))::(((FStar_Getopt.noshort), ("hint_file"), (FStar_Getopt.OneArg ((((fun _0_37 -> Path (_0_37))), ("[path]")))), ("Read/write hints to <path> (instead of module-specific hints files)")))::(((FStar_Getopt.noshort), ("in"), (FStar_Getopt.ZeroArgs ((fun uu____1948 -> Bool (true)))), ("Legacy interactive mode; reads input from stdin")))::(((FStar_Getopt.noshort), ("ide"), (FStar_Getopt.ZeroArgs ((fun uu____1962 -> Bool (true)))), ("JSON-based interactive mode for IDEs")))::(((FStar_Getopt.noshort), ("include"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1980 = (

let uu____1983 = (

let uu____1986 = (get_include ())
in (FStar_List.map (fun _0_38 -> String (_0_38)) uu____1986))
in (FStar_List.append uu____1983 ((Path (s))::[])))
in List (uu____1980)))), ("[path]")))), ("A directory in which to search for files included on the command line")))::(((FStar_Getopt.noshort), ("indent"), (FStar_Getopt.ZeroArgs ((fun uu____2002 -> Bool (true)))), ("Parses and outputs the files on the command line")))::(((FStar_Getopt.noshort), ("initial_fuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____2020 = (FStar_Util.int_of_string x)
in Int (uu____2020)))), ("[non-negative integer]")))), ("Number of unrolling of recursive functions to try initially (default 2)")))::(((FStar_Getopt.noshort), ("initial_ifuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____2038 = (FStar_Util.int_of_string x)
in Int (uu____2038)))), ("[non-negative integer]")))), ("Number of unrolling of inductive datatypes to try at first (default 1)")))::(((FStar_Getopt.noshort), ("inline_arith"), (FStar_Getopt.ZeroArgs ((fun uu____2052 -> Bool (true)))), ("Inline definitions of arithmetic functions in the SMT encoding")))::(((FStar_Getopt.noshort), ("lax"), (FStar_Getopt.ZeroArgs ((fun uu____2066 -> Bool (true)))), ("Run the lax-type checker only (admit all verification conditions)")))::(((FStar_Getopt.noshort), ("load"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____2084 = (

let uu____2087 = (

let uu____2090 = (get_load ())
in (FStar_List.map (fun _0_39 -> String (_0_39)) uu____2090))
in (FStar_List.append uu____2087 ((Path (s))::[])))
in List (uu____2084)))), ("[module]")))), ("Load compiled module")))::(((FStar_Getopt.noshort), ("log_types"), (FStar_Getopt.ZeroArgs ((fun uu____2106 -> Bool (true)))), ("Print types computed for data/val/let-bindings")))::(((FStar_Getopt.noshort), ("log_queries"), (FStar_Getopt.ZeroArgs ((fun uu____2120 -> Bool (true)))), ("Log the Z3 queries in several queries-*.smt2 files, as we go")))::(((FStar_Getopt.noshort), ("max_fuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____2138 = (FStar_Util.int_of_string x)
in Int (uu____2138)))), ("[non-negative integer]")))), ("Number of unrolling of recursive functions to try at most (default 8)")))::(((FStar_Getopt.noshort), ("max_ifuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____2156 = (FStar_Util.int_of_string x)
in Int (uu____2156)))), ("[non-negative integer]")))), ("Number of unrolling of inductive datatypes to try at most (default 2)")))::(((FStar_Getopt.noshort), ("min_fuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____2174 = (FStar_Util.int_of_string x)
in Int (uu____2174)))), ("[non-negative integer]")))), ("Minimum number of unrolling of recursive functions to try (default 1)")))::(((FStar_Getopt.noshort), ("MLish"), (FStar_Getopt.ZeroArgs ((fun uu____2188 -> Bool (true)))), ("Trigger various specializations for compiling the F* compiler itself (not meant for user code)")))::(((FStar_Getopt.noshort), ("n_cores"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____2206 = (FStar_Util.int_of_string x)
in Int (uu____2206)))), ("[positive integer]")))), ("Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")))::(((FStar_Getopt.noshort), ("no_default_includes"), (FStar_Getopt.ZeroArgs ((fun uu____2220 -> Bool (true)))), ("Ignore the default module search paths")))::(((FStar_Getopt.noshort), ("no_extract"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____2238 = (

let uu____2241 = (

let uu____2244 = (get_no_extract ())
in (x)::uu____2244)
in (FStar_All.pipe_right uu____2241 (FStar_List.map (fun _0_40 -> String (_0_40)))))
in List (uu____2238)))), ("[module name]")))), ("Do not extract code from this module")))::(((FStar_Getopt.noshort), ("no_location_info"), (FStar_Getopt.ZeroArgs ((fun uu____2264 -> Bool (true)))), ("Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")))::(((FStar_Getopt.noshort), ("odir"), (FStar_Getopt.OneArg ((((fun p -> (

let uu____2282 = (validate_dir p)
in Path (uu____2282)))), ("[dir]")))), ("Place output in directory [dir]")))::(((FStar_Getopt.noshort), ("prims"), (FStar_Getopt.OneArg ((((fun _0_41 -> String (_0_41))), ("file")))), ("")))::(((FStar_Getopt.noshort), ("print_bound_var_types"), (FStar_Getopt.ZeroArgs ((fun uu____2310 -> Bool (true)))), ("Print the types of bound variables")))::(((FStar_Getopt.noshort), ("print_effect_args"), (FStar_Getopt.ZeroArgs ((fun uu____2324 -> Bool (true)))), ("Print inferred predicate transformers for all computation types")))::(((FStar_Getopt.noshort), ("print_fuels"), (FStar_Getopt.ZeroArgs ((fun uu____2338 -> Bool (true)))), ("Print the fuel amounts used for each successful query")))::(((FStar_Getopt.noshort), ("print_full_names"), (FStar_Getopt.ZeroArgs ((fun uu____2352 -> Bool (true)))), ("Print full names of variables")))::(((FStar_Getopt.noshort), ("print_implicits"), (FStar_Getopt.ZeroArgs ((fun uu____2366 -> Bool (true)))), ("Print implicit arguments")))::(((FStar_Getopt.noshort), ("print_universes"), (FStar_Getopt.ZeroArgs ((fun uu____2380 -> Bool (true)))), ("Print universes")))::(((FStar_Getopt.noshort), ("print_z3_statistics"), (FStar_Getopt.ZeroArgs ((fun uu____2394 -> Bool (true)))), ("Print Z3 statistics for each SMT query")))::(((FStar_Getopt.noshort), ("prn"), (FStar_Getopt.ZeroArgs ((fun uu____2408 -> Bool (true)))), ("Print full names (deprecated; use --print_full_names instead)")))::(((FStar_Getopt.noshort), ("record_hints"), (FStar_Getopt.ZeroArgs ((fun uu____2422 -> Bool (true)))), ("Record a database of hints for efficient proof replay")))::(((FStar_Getopt.noshort), ("check_hints"), (FStar_Getopt.ZeroArgs ((fun uu____2436 -> Bool (true)))), ("Check new hints for replayability")))::(((FStar_Getopt.noshort), ("reuse_hint_for"), (FStar_Getopt.OneArg ((((fun _0_42 -> String (_0_42))), ("top-level name in the current module")))), ("Optimistically, attempt using the recorded hint for \'f\' when trying to verify some other term \'g\'")))::(((FStar_Getopt.noshort), ("show_signatures"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____2468 = (

let uu____2471 = (

let uu____2474 = (get_show_signatures ())
in (x)::uu____2474)
in (FStar_All.pipe_right uu____2471 (FStar_List.map (fun _0_43 -> String (_0_43)))))
in List (uu____2468)))), ("[module name]")))), ("Show the checked signatures for all top-level symbols in the module")))::(((FStar_Getopt.noshort), ("silent"), (FStar_Getopt.ZeroArgs ((fun uu____2494 -> Bool (true)))), (" ")))::(((FStar_Getopt.noshort), ("smt"), (FStar_Getopt.OneArg ((((fun _0_44 -> Path (_0_44))), ("[path]")))), ("Path to the Z3 SMT solver (we could eventually support other solvers)")))::(((FStar_Getopt.noshort), ("smtencoding.elim_box"), (FStar_Getopt.OneArg ((((string_as_bool "smtencoding.elim_box")), ("true|false")))), ("Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default \'false\')")))::(((FStar_Getopt.noshort), ("smtencoding.nl_arith_repr"), (FStar_Getopt.OneArg ((((fun _0_45 -> String (_0_45))), ("native|wrapped|boxwrap")))), ("Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if \'boxwrap\' use \'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus\'; \n\t\tif \'native\' use \'*, div, mod\';\n\t\tif \'wrapped\' use \'_mul, _div, _mod : Int*Int -> Int\'; \n\t\t(default \'boxwrap\')")))::(((FStar_Getopt.noshort), ("smtencoding.l_arith_repr"), (FStar_Getopt.OneArg ((((fun _0_46 -> String (_0_46))), ("native|boxwrap")))), ("Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if \'boxwrap\', use \'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus\'; \n\t\tif \'native\', use \'+, -, -\'; \n\t\t(default \'boxwrap\')")))::(((FStar_Getopt.noshort), ("split_cases"), (FStar_Getopt.OneArg ((((fun n1 -> (

let uu____2568 = (FStar_Util.int_of_string n1)
in Int (uu____2568)))), ("[positive integer]")))), ("Partition VC of a match into groups of [n] cases")))::(((FStar_Getopt.noshort), ("timing"), (FStar_Getopt.ZeroArgs ((fun uu____2582 -> Bool (true)))), ("Print the time it takes to verify each top-level definition")))::(((FStar_Getopt.noshort), ("trace_error"), (FStar_Getopt.ZeroArgs ((fun uu____2596 -> Bool (true)))), ("Don\'t print an error message; show an exception trace instead")))::(((FStar_Getopt.noshort), ("ugly"), (FStar_Getopt.ZeroArgs ((fun uu____2610 -> Bool (true)))), ("Emit output formatted for debugging")))::(((FStar_Getopt.noshort), ("unthrottle_inductives"), (FStar_Getopt.ZeroArgs ((fun uu____2624 -> Bool (true)))), ("Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")))::(((FStar_Getopt.noshort), ("use_eq_at_higher_order"), (FStar_Getopt.ZeroArgs ((fun uu____2638 -> Bool (true)))), ("Use equality constraints when comparing higher-order types (Temporary)")))::(((FStar_Getopt.noshort), ("use_hints"), (FStar_Getopt.ZeroArgs ((fun uu____2652 -> Bool (true)))), ("Use a previously recorded hints database for proof replay")))::(((FStar_Getopt.noshort), ("no_tactics"), (FStar_Getopt.ZeroArgs ((fun uu____2666 -> Bool (true)))), ("Do not run the tactic engine before discharging a VC")))::(((FStar_Getopt.noshort), ("using_facts_from"), (FStar_Getopt.OneArg (((cons_using_facts_from), ("[namespace | fact id]")))), ("Implies --z3refresh; prunes the context to include facts from the given namespace of fact id (multiple uses of this option will prune the context to include those facts that match any of the provided namespaces / fact ids")))::(((FStar_Getopt.noshort), ("verify_all"), (FStar_Getopt.ZeroArgs ((fun uu____2694 -> Bool (true)))), ("With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.")))::(((FStar_Getopt.noshort), ("verify_module"), (FStar_Getopt.OneArg (((cons_verify_module), ("[module name]")))), ("Name of the module to verify")))::(((FStar_Getopt.noshort), ("__temp_no_proj"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____2726 = (

let uu____2729 = (

let uu____2732 = (get___temp_no_proj ())
in (x)::uu____2732)
in (FStar_All.pipe_right uu____2729 (FStar_List.map (fun _0_47 -> String (_0_47)))))
in List (uu____2726)))), ("[module name]")))), ("Don\'t generate projectors for this module")))::((('v'), ("version"), (FStar_Getopt.ZeroArgs ((fun uu____2753 -> ((display_version ());
(FStar_All.exit (Prims.parse_int "0"));
)))), ("Display version number")))::(((FStar_Getopt.noshort), ("warn_default_effects"), (FStar_Getopt.ZeroArgs ((fun uu____2768 -> Bool (true)))), ("Warn when (a -> b) is desugared to (a -> Tot b)")))::(((FStar_Getopt.noshort), ("z3cliopt"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____2786 = (

let uu____2789 = (

let uu____2792 = (get_z3cliopt ())
in (FStar_List.append uu____2792 ((s)::[])))
in (FStar_All.pipe_right uu____2789 (FStar_List.map (fun _0_48 -> String (_0_48)))))
in List (uu____2786)))), ("[option]")))), ("Z3 command line options")))::(((FStar_Getopt.noshort), ("z3refresh"), (FStar_Getopt.ZeroArgs ((fun uu____2812 -> Bool (true)))), ("Restart Z3 after each query; useful for ensuring proof robustness")))::(((FStar_Getopt.noshort), ("z3rlimit"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____2830 = (FStar_Util.int_of_string s)
in Int (uu____2830)))), ("[positive integer]")))), ("Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")))::(((FStar_Getopt.noshort), ("z3rlimit_factor"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____2848 = (FStar_Util.int_of_string s)
in Int (uu____2848)))), ("[positive integer]")))), ("Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")))::(((FStar_Getopt.noshort), ("z3seed"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____2866 = (FStar_Util.int_of_string s)
in Int (uu____2866)))), ("[positive integer]")))), ("Set the Z3 random seed (default 0)")))::(((FStar_Getopt.noshort), ("__no_positivity"), (FStar_Getopt.ZeroArgs ((fun uu____2880 -> Bool (true)))), ("Don\'t check positivity of inductive types")))::(((FStar_Getopt.noshort), ("__ml_no_eta_expand_coertions"), (FStar_Getopt.ZeroArgs ((fun uu____2894 -> Bool (true)))), ("Do not eta-expand coertions in generated OCaml")))::[]
in (

let uu____2905 = (FStar_List.map mk_spec specs1)
in ((('h'), ("help"), (FStar_Getopt.ZeroArgs ((fun x -> ((display_usage_aux specs1);
(FStar_All.exit (Prims.parse_int "0"));
)))), ("Display this information")))::uu____2905)))
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
| uu____2945 -> begin
((FStar_Util.print_string "Wrong argument to codegen flag\n");
(

let uu____2948 = (specs ())
in (display_usage_aux uu____2948));
(FStar_All.exit (Prims.parse_int "1"));
)
end))
and string_as_bool : Prims.string  ->  Prims.string  ->  option_val = (fun option_name uu___55_2962 -> (match (uu___55_2962) with
| "true" -> begin
Bool (true)
end
| "false" -> begin
Bool (false)
end
| uu____2963 -> begin
((FStar_Util.print1 "Wrong argument to %s\n" option_name);
(

let uu____2966 = (specs ())
in (display_usage_aux uu____2966));
(FStar_All.exit (Prims.parse_int "1"));
)
end))
and validate_dir : Prims.string  ->  Prims.string = (fun p -> ((FStar_Util.mkdir false p);
p;
))


let docs : Prims.unit  ->  (Prims.string * Prims.string) Prims.list = (fun uu____2990 -> (

let uu____2991 = (specs ())
in (FStar_List.map (fun uu____3023 -> (match (uu____3023) with
| (uu____3038, name, uu____3040, doc) -> begin
((name), (doc))
end)) uu____2991)))


let settable : Prims.string  ->  Prims.bool = (fun uu___56_3049 -> (match (uu___56_3049) with
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
| uu____3050 -> begin
false
end))


let resettable : Prims.string  ->  Prims.bool = (fun s -> (((settable s) || (s = "z3seed")) || (s = "z3cliopt")))


let all_specs : FStar_Getopt.opt Prims.list = (specs ())


let settable_specs : (FStar_BaseTypes.char * Prims.string * Prims.unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____3098 -> (match (uu____3098) with
| (uu____3109, x, uu____3111, uu____3112) -> begin
(settable x)
end))))


let resettable_specs : (FStar_BaseTypes.char * Prims.string * Prims.unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____3158 -> (match (uu____3158) with
| (uu____3169, x, uu____3171, uu____3172) -> begin
(resettable x)
end))))


let display_usage : Prims.unit  ->  Prims.unit = (fun uu____3180 -> (

let uu____3181 = (specs ())
in (display_usage_aux uu____3181)))


let fstar_home : Prims.unit  ->  Prims.string = (fun uu____3197 -> (

let uu____3198 = (get_fstar_home ())
in (match (uu____3198) with
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
| File_argument (uu____3212) -> begin
true
end
| uu____3213 -> begin
false
end))


let __proj__File_argument__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| File_argument (uu____3221) -> begin
uu____3221
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
| uu____3257 -> begin
(FStar_Getopt.parse_string specs1 (fun s1 -> (FStar_Pervasives.raise (File_argument (s1)))) s)
end)
end)
with
| File_argument (s1) -> begin
(

let uu____3267 = (FStar_Util.format1 "File %s is not a valid option" s1)
in FStar_Getopt.Error (uu____3267))
end))


let file_list_ : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let parse_cmd_line : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____3284 -> (

let res = (

let uu____3286 = (specs ())
in (FStar_Getopt.parse_cmdline uu____3286 (fun i -> (

let uu____3292 = (

let uu____3295 = (FStar_ST.read file_list_)
in (FStar_List.append uu____3295 ((i)::[])))
in (FStar_ST.write file_list_ uu____3292)))))
in (

let uu____3302 = (

let uu____3305 = (FStar_ST.read file_list_)
in (FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____3305))
in ((res), (uu____3302)))))


let file_list : Prims.unit  ->  Prims.string Prims.list = (fun uu____3317 -> (FStar_ST.read file_list_))


let restore_cmd_line_options : Prims.bool  ->  FStar_Getopt.parse_cmdline_res = (fun should_clear -> (

let old_verify_module = (get_verify_module ())
in ((match (should_clear) with
| true -> begin
(clear ())
end
| uu____3328 -> begin
(init ())
end);
(

let r = (

let uu____3330 = (specs ())
in (FStar_Getopt.parse_cmdline uu____3330 (fun x -> ())))
in ((

let uu____3336 = (

let uu____3341 = (

let uu____3342 = (FStar_List.map (fun _0_49 -> String (_0_49)) old_verify_module)
in List (uu____3342))
in (("verify_module"), (uu____3341)))
in (set_option' uu____3336));
r;
));
)))


let should_verify : Prims.string  ->  Prims.bool = (fun m -> (

let uu____3349 = (get_lax ())
in (match (uu____3349) with
| true -> begin
false
end
| uu____3350 -> begin
(

let uu____3351 = (get_verify_all ())
in (match (uu____3351) with
| true -> begin
true
end
| uu____3352 -> begin
(

let uu____3353 = (get_verify_module ())
in (match (uu____3353) with
| [] -> begin
(

let uu____3356 = (file_list ())
in (FStar_List.existsML (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let f2 = (

let uu____3365 = (

let uu____3366 = (

let uu____3367 = (

let uu____3368 = (FStar_Util.get_file_extension f1)
in (FStar_String.length uu____3368))
in ((FStar_String.length f1) - uu____3367))
in (uu____3366 - (Prims.parse_int "1")))
in (FStar_String.substring f1 (Prims.parse_int "0") uu____3365))
in ((FStar_String.lowercase f2) = m)))) uu____3356))
end
| l -> begin
(FStar_List.contains (FStar_String.lowercase m) l)
end))
end))
end)))


let dont_gen_projectors : Prims.string  ->  Prims.bool = (fun m -> (

let uu____3376 = (get___temp_no_proj ())
in (FStar_List.contains m uu____3376)))


let should_print_message : Prims.string  ->  Prims.bool = (fun m -> (

let uu____3383 = (should_verify m)
in (match (uu____3383) with
| true -> begin
(m <> "Prims")
end
| uu____3384 -> begin
false
end)))


let include_path : Prims.unit  ->  Prims.string Prims.list = (fun uu____3390 -> (

let uu____3391 = (get_no_default_includes ())
in (match (uu____3391) with
| true -> begin
(get_include ())
end
| uu____3394 -> begin
(

let h = (fstar_home ())
in (

let defs = universe_include_path_base_dirs
in (

let uu____3399 = (

let uu____3402 = (FStar_All.pipe_right defs (FStar_List.map (fun x -> (Prims.strcat h x))))
in (FStar_All.pipe_right uu____3402 (FStar_List.filter FStar_Util.file_exists)))
in (

let uu____3415 = (

let uu____3418 = (get_include ())
in (FStar_List.append uu____3418 ((".")::[])))
in (FStar_List.append uu____3399 uu____3415)))))
end)))


let find_file : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun filename -> (

let uu____3427 = (FStar_Util.is_path_absolute filename)
in (match (uu____3427) with
| true -> begin
(match ((FStar_Util.file_exists filename)) with
| true -> begin
FStar_Pervasives_Native.Some (filename)
end
| uu____3432 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____3433 -> begin
(

let uu____3434 = (

let uu____3437 = (include_path ())
in (FStar_List.rev uu____3437))
in (FStar_Util.find_map uu____3434 (fun p -> (

let path = (FStar_Util.join_paths p filename)
in (match ((FStar_Util.file_exists path)) with
| true -> begin
FStar_Pervasives_Native.Some (path)
end
| uu____3446 -> begin
FStar_Pervasives_Native.None
end)))))
end)))


let prims : Prims.unit  ->  Prims.string = (fun uu____3450 -> (

let uu____3451 = (get_prims ())
in (match (uu____3451) with
| FStar_Pervasives_Native.None -> begin
(

let filename = "prims.fst"
in (

let uu____3455 = (find_file filename)
in (match (uu____3455) with
| FStar_Pervasives_Native.Some (result) -> begin
result
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3459 = (

let uu____3460 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in FStar_Util.Failure (uu____3460))
in (FStar_Pervasives.raise uu____3459))
end)))
end
| FStar_Pervasives_Native.Some (x) -> begin
x
end)))


let prims_basename : Prims.unit  ->  Prims.string = (fun uu____3465 -> (

let uu____3466 = (prims ())
in (FStar_Util.basename uu____3466)))


let pervasives : Prims.unit  ->  Prims.string = (fun uu____3470 -> (

let filename = "FStar.Pervasives.fst"
in (

let uu____3472 = (find_file filename)
in (match (uu____3472) with
| FStar_Pervasives_Native.Some (result) -> begin
result
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3476 = (

let uu____3477 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in FStar_Util.Failure (uu____3477))
in (FStar_Pervasives.raise uu____3476))
end))))


let pervasives_basename : Prims.unit  ->  Prims.string = (fun uu____3481 -> (

let uu____3482 = (pervasives ())
in (FStar_Util.basename uu____3482)))


let pervasives_native_basename : Prims.unit  ->  Prims.string = (fun uu____3486 -> (

let filename = "FStar.Pervasives.Native.fst"
in (

let uu____3488 = (find_file filename)
in (match (uu____3488) with
| FStar_Pervasives_Native.Some (result) -> begin
(FStar_Util.basename result)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3492 = (

let uu____3493 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in FStar_Util.Failure (uu____3493))
in (FStar_Pervasives.raise uu____3492))
end))))


let prepend_output_dir : Prims.string  ->  Prims.string = (fun fname -> (

let uu____3498 = (get_odir ())
in (match (uu____3498) with
| FStar_Pervasives_Native.None -> begin
fname
end
| FStar_Pervasives_Native.Some (x) -> begin
(Prims.strcat x (Prims.strcat "/" fname))
end)))


let __temp_no_proj : Prims.string  ->  Prims.bool = (fun s -> (

let uu____3506 = (get___temp_no_proj ())
in (FStar_All.pipe_right uu____3506 (FStar_List.contains s))))


let admit_smt_queries : Prims.unit  ->  Prims.bool = (fun uu____3514 -> (get_admit_smt_queries ()))


let admit_except : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3520 -> (get_admit_except ()))


let check_hints : Prims.unit  ->  Prims.bool = (fun uu____3524 -> (get_check_hints ()))


let codegen : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3530 -> (get_codegen ()))


let codegen_libs : Prims.unit  ->  Prims.string Prims.list Prims.list = (fun uu____3538 -> (

let uu____3539 = (get_codegen_lib ())
in (FStar_All.pipe_right uu____3539 (FStar_List.map (fun x -> (FStar_Util.split x "."))))))


let debug_any : Prims.unit  ->  Prims.bool = (fun uu____3555 -> (

let uu____3556 = (get_debug ())
in (uu____3556 <> [])))


let debug_at_level : Prims.string  ->  debug_level_t  ->  Prims.bool = (fun modul level -> (((modul = "") || (

let uu____3570 = (get_debug ())
in (FStar_All.pipe_right uu____3570 (FStar_List.contains modul)))) && (debug_level_geq level)))


let dep : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3580 -> (get_dep ()))


let detail_errors : Prims.unit  ->  Prims.bool = (fun uu____3584 -> (get_detail_errors ()))


let detail_hint_replay : Prims.unit  ->  Prims.bool = (fun uu____3588 -> (get_detail_hint_replay ()))


let doc : Prims.unit  ->  Prims.bool = (fun uu____3592 -> (get_doc ()))


let dump_module : Prims.string  ->  Prims.bool = (fun s -> (

let uu____3597 = (get_dump_module ())
in (FStar_All.pipe_right uu____3597 (FStar_List.contains s))))


let eager_inference : Prims.unit  ->  Prims.bool = (fun uu____3605 -> (get_eager_inference ()))


let explicit_deps : Prims.unit  ->  Prims.bool = (fun uu____3609 -> (get_explicit_deps ()))


let extract_all : Prims.unit  ->  Prims.bool = (fun uu____3613 -> (get_extract_all ()))


let fs_typ_app : Prims.string  ->  Prims.bool = (fun filename -> (

let uu____3618 = (FStar_ST.read light_off_files)
in (FStar_List.contains filename uu____3618)))


let full_context_dependency : Prims.unit  ->  Prims.bool = (fun uu____3626 -> true)


let hide_genident_nums : Prims.unit  ->  Prims.bool = (fun uu____3630 -> (get_hide_genident_nums ()))


let hide_uvar_nums : Prims.unit  ->  Prims.bool = (fun uu____3634 -> (get_hide_uvar_nums ()))


let hint_info : Prims.unit  ->  Prims.bool = (fun uu____3638 -> (get_hint_info ()))


let hint_file : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3644 -> (get_hint_file ()))


let ide : Prims.unit  ->  Prims.bool = (fun uu____3648 -> (get_ide ()))


let indent : Prims.unit  ->  Prims.bool = (fun uu____3652 -> (get_indent ()))


let initial_fuel : Prims.unit  ->  Prims.int = (fun uu____3656 -> (

let uu____3657 = (get_initial_fuel ())
in (

let uu____3658 = (get_max_fuel ())
in (Prims.min uu____3657 uu____3658))))


let initial_ifuel : Prims.unit  ->  Prims.int = (fun uu____3662 -> (

let uu____3663 = (get_initial_ifuel ())
in (

let uu____3664 = (get_max_ifuel ())
in (Prims.min uu____3663 uu____3664))))


let interactive : Prims.unit  ->  Prims.bool = (fun uu____3668 -> ((get_in ()) || (get_ide ())))


let lax : Prims.unit  ->  Prims.bool = (fun uu____3672 -> (get_lax ()))


let load : Prims.unit  ->  Prims.string Prims.list = (fun uu____3678 -> (get_load ()))


let legacy_interactive : Prims.unit  ->  Prims.bool = (fun uu____3682 -> (get_in ()))


let log_queries : Prims.unit  ->  Prims.bool = (fun uu____3686 -> (get_log_queries ()))


let log_types : Prims.unit  ->  Prims.bool = (fun uu____3690 -> (get_log_types ()))


let max_fuel : Prims.unit  ->  Prims.int = (fun uu____3694 -> (get_max_fuel ()))


let max_ifuel : Prims.unit  ->  Prims.int = (fun uu____3698 -> (get_max_ifuel ()))


let min_fuel : Prims.unit  ->  Prims.int = (fun uu____3702 -> (get_min_fuel ()))


let ml_ish : Prims.unit  ->  Prims.bool = (fun uu____3706 -> (get_MLish ()))


let set_ml_ish : Prims.unit  ->  Prims.unit = (fun uu____3710 -> (set_option "MLish" (Bool (true))))


let n_cores : Prims.unit  ->  Prims.int = (fun uu____3714 -> (get_n_cores ()))


let no_default_includes : Prims.unit  ->  Prims.bool = (fun uu____3718 -> (get_no_default_includes ()))


let no_extract : Prims.string  ->  Prims.bool = (fun s -> (

let uu____3723 = (get_no_extract ())
in (FStar_All.pipe_right uu____3723 (FStar_List.contains s))))


let no_location_info : Prims.unit  ->  Prims.bool = (fun uu____3731 -> (get_no_location_info ()))


let output_dir : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3737 -> (get_odir ()))


let ugly : Prims.unit  ->  Prims.bool = (fun uu____3741 -> (get_ugly ()))


let print_bound_var_types : Prims.unit  ->  Prims.bool = (fun uu____3745 -> (get_print_bound_var_types ()))


let print_effect_args : Prims.unit  ->  Prims.bool = (fun uu____3749 -> (get_print_effect_args ()))


let print_fuels : Prims.unit  ->  Prims.bool = (fun uu____3753 -> (get_print_fuels ()))


let print_implicits : Prims.unit  ->  Prims.bool = (fun uu____3757 -> (get_print_implicits ()))


let print_real_names : Prims.unit  ->  Prims.bool = (fun uu____3761 -> ((get_prn ()) || (get_print_full_names ())))


let print_universes : Prims.unit  ->  Prims.bool = (fun uu____3765 -> (get_print_universes ()))


let print_z3_statistics : Prims.unit  ->  Prims.bool = (fun uu____3769 -> (get_print_z3_statistics ()))


let record_hints : Prims.unit  ->  Prims.bool = (fun uu____3773 -> (get_record_hints ()))


let reuse_hint_for : Prims.unit  ->  Prims.string FStar_Pervasives_Native.option = (fun uu____3779 -> (get_reuse_hint_for ()))


let silent : Prims.unit  ->  Prims.bool = (fun uu____3783 -> (get_silent ()))


let smtencoding_elim_box : Prims.unit  ->  Prims.bool = (fun uu____3787 -> (get_smtencoding_elim_box ()))


let smtencoding_nl_arith_native : Prims.unit  ->  Prims.bool = (fun uu____3791 -> (

let uu____3792 = (get_smtencoding_nl_arith_repr ())
in (uu____3792 = "native")))


let smtencoding_nl_arith_wrapped : Prims.unit  ->  Prims.bool = (fun uu____3796 -> (

let uu____3797 = (get_smtencoding_nl_arith_repr ())
in (uu____3797 = "wrapped")))


let smtencoding_nl_arith_default : Prims.unit  ->  Prims.bool = (fun uu____3801 -> (

let uu____3802 = (get_smtencoding_nl_arith_repr ())
in (uu____3802 = "boxwrap")))


let smtencoding_l_arith_native : Prims.unit  ->  Prims.bool = (fun uu____3806 -> (

let uu____3807 = (get_smtencoding_l_arith_repr ())
in (uu____3807 = "native")))


let smtencoding_l_arith_default : Prims.unit  ->  Prims.bool = (fun uu____3811 -> (

let uu____3812 = (get_smtencoding_l_arith_repr ())
in (uu____3812 = "boxwrap")))


let split_cases : Prims.unit  ->  Prims.int = (fun uu____3816 -> (get_split_cases ()))


let timing : Prims.unit  ->  Prims.bool = (fun uu____3820 -> (get_timing ()))


let trace_error : Prims.unit  ->  Prims.bool = (fun uu____3824 -> (get_trace_error ()))


let unthrottle_inductives : Prims.unit  ->  Prims.bool = (fun uu____3828 -> (get_unthrottle_inductives ()))


let use_eq_at_higher_order : Prims.unit  ->  Prims.bool = (fun uu____3832 -> (get_use_eq_at_higher_order ()))


let use_hints : Prims.unit  ->  Prims.bool = (fun uu____3836 -> (get_use_hints ()))


let use_tactics : Prims.unit  ->  Prims.bool = (fun uu____3840 -> (get_use_tactics ()))


let using_facts_from : Prims.unit  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun uu____3848 -> (get_using_facts_from ()))


let verify_all : Prims.unit  ->  Prims.bool = (fun uu____3852 -> (get_verify_all ()))


let verify_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____3858 -> (get_verify_module ()))


let warn_default_effects : Prims.unit  ->  Prims.bool = (fun uu____3862 -> (get_warn_default_effects ()))


let z3_exe : Prims.unit  ->  Prims.string = (fun uu____3866 -> (

let uu____3867 = (get_smt ())
in (match (uu____3867) with
| FStar_Pervasives_Native.None -> begin
(FStar_Platform.exe "z3")
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let z3_cliopt : Prims.unit  ->  Prims.string Prims.list = (fun uu____3876 -> (get_z3cliopt ()))


let z3_refresh : Prims.unit  ->  Prims.bool = (fun uu____3880 -> (get_z3refresh ()))


let z3_rlimit : Prims.unit  ->  Prims.int = (fun uu____3884 -> (get_z3rlimit ()))


let z3_rlimit_factor : Prims.unit  ->  Prims.int = (fun uu____3888 -> (get_z3rlimit_factor ()))


let z3_seed : Prims.unit  ->  Prims.int = (fun uu____3892 -> (get_z3seed ()))


let no_positivity : Prims.unit  ->  Prims.bool = (fun uu____3896 -> (get_no_positivity ()))


let ml_no_eta_expand_coertions : Prims.unit  ->  Prims.bool = (fun uu____3900 -> (get_ml_no_eta_expand_coertions ()))


let should_extract : Prims.string  ->  Prims.bool = (fun m -> ((

let uu____3907 = (no_extract m)
in (not (uu____3907))) && ((extract_all ()) || (

let uu____3910 = (get_extract_module ())
in (match (uu____3910) with
| [] -> begin
(

let uu____3913 = (get_extract_namespace ())
in (match (uu____3913) with
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




