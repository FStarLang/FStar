
open Prims
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
| uu____7 -> begin
false
end))


let uu___is_Medium : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Medium -> begin
true
end
| uu____11 -> begin
false
end))


let uu___is_High : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| High -> begin
true
end
| uu____15 -> begin
false
end))


let uu___is_Extreme : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Extreme -> begin
true
end
| uu____19 -> begin
false
end))


let uu___is_Other : debug_level_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Other (_0) -> begin
true
end
| uu____24 -> begin
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
| uu____52 -> begin
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
| uu____64 -> begin
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
| uu____76 -> begin
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
| uu____88 -> begin
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
| uu____101 -> begin
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
| uu____115 -> begin
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
| uu____119 -> begin
false
end))


let uu___is_Reset : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reset -> begin
true
end
| uu____123 -> begin
false
end))


let uu___is_Restore : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Restore -> begin
true
end
| uu____127 -> begin
false
end))


let __unit_tests__ : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let __unit_tests : Prims.unit  ->  Prims.bool = (fun uu____133 -> (FStar_ST.read __unit_tests__))


let __set_unit_tests : Prims.unit  ->  Prims.unit = (fun uu____138 -> (FStar_ST.write __unit_tests__ true))


let __clear_unit_tests : Prims.unit  ->  Prims.unit = (fun uu____143 -> (FStar_ST.write __unit_tests__ false))


let as_bool : option_val  ->  Prims.bool = (fun uu___51_148 -> (match (uu___51_148) with
| Bool (b) -> begin
b
end
| uu____150 -> begin
(failwith "Impos: expected Bool")
end))


let as_int : option_val  ->  Prims.int = (fun uu___52_153 -> (match (uu___52_153) with
| Int (b) -> begin
b
end
| uu____155 -> begin
(failwith "Impos: expected Int")
end))


let as_string : option_val  ->  Prims.string = (fun uu___53_158 -> (match (uu___53_158) with
| String (b) -> begin
b
end
| Path (b) -> begin
(FStar_Common.try_convert_file_name_to_mixed b)
end
| uu____161 -> begin
(failwith "Impos: expected String")
end))


let as_list = (fun as_t uu___54_177 -> (match (uu___54_177) with
| List (ts) -> begin
(FStar_All.pipe_right ts (FStar_List.map as_t))
end
| uu____184 -> begin
(failwith "Impos: expected List")
end))


let as_option = (fun as_t uu___55_201 -> (match (uu___55_201) with
| Unset -> begin
None
end
| v1 -> begin
(

let uu____205 = (as_t v1)
in Some (uu____205))
end))


let fstar_options : option_val FStar_Util.smap Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let peek : Prims.unit  ->  option_val FStar_Util.smap = (fun uu____217 -> (

let uu____218 = (FStar_ST.read fstar_options)
in (FStar_List.hd uu____218)))


let pop : Prims.unit  ->  Prims.unit = (fun uu____228 -> (

let uu____229 = (FStar_ST.read fstar_options)
in (match (uu____229) with
| ([]) | ((_)::[]) -> begin
(failwith "TOO MANY POPS!")
end
| (uu____240)::tl1 -> begin
(FStar_ST.write fstar_options tl1)
end)))


let push : Prims.unit  ->  Prims.unit = (fun uu____252 -> (

let uu____253 = (

let uu____256 = (

let uu____258 = (peek ())
in (FStar_Util.smap_copy uu____258))
in (

let uu____260 = (FStar_ST.read fstar_options)
in (uu____256)::uu____260))
in (FStar_ST.write fstar_options uu____253)))


let set_option : Prims.string  ->  option_val  ->  Prims.unit = (fun k v1 -> (

let uu____278 = (peek ())
in (FStar_Util.smap_add uu____278 k v1)))


let set_option' : (Prims.string * option_val)  ->  Prims.unit = (fun uu____284 -> (match (uu____284) with
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

let uu____312 = (

let uu____314 = (FStar_ST.read light_off_files)
in (filename)::uu____314)
in (FStar_ST.write light_off_files uu____312)))


let defaults : (Prims.string * option_val) Prims.list = ((("__temp_no_proj"), (List ([]))))::((("_fstar_home"), (String (""))))::((("_include_path"), (List ([]))))::((("admit_smt_queries"), (Bool (false))))::((("cardinality"), (String ("off"))))::((("codegen"), (Unset)))::((("codegen-lib"), (List ([]))))::((("debug"), (List ([]))))::((("debug_level"), (List ([]))))::((("dep"), (Unset)))::((("detail_errors"), (Bool (false))))::((("doc"), (Bool (false))))::((("dump_module"), (List ([]))))::((("eager_inference"), (Bool (false))))::((("explicit_deps"), (Bool (false))))::((("extract_all"), (Bool (false))))::((("extract_module"), (List ([]))))::((("extract_namespace"), (List ([]))))::((("fs_typ_app"), (Bool (false))))::((("fstar_home"), (Unset)))::((("full_context_dependency"), (Bool (true))))::((("hide_genident_nums"), (Bool (false))))::((("hide_uvar_nums"), (Bool (false))))::((("hint_info"), (Bool (false))))::((("in"), (Bool (false))))::((("ide"), (Bool (false))))::((("include"), (List ([]))))::((("indent"), (Bool (false))))::((("initial_fuel"), (Int ((Prims.parse_int "2")))))::((("initial_ifuel"), (Int ((Prims.parse_int "1")))))::((("inline_arith"), (Bool (false))))::((("lax"), (Bool (false))))::((("log_queries"), (Bool (false))))::((("log_types"), (Bool (false))))::((("max_fuel"), (Int ((Prims.parse_int "8")))))::((("max_ifuel"), (Int ((Prims.parse_int "2")))))::((("min_fuel"), (Int ((Prims.parse_int "1")))))::((("MLish"), (Bool (false))))::((("n_cores"), (Int ((Prims.parse_int "1")))))::((("no_default_includes"), (Bool (false))))::((("no_extract"), (List ([]))))::((("no_location_info"), (Bool (false))))::((("no_warn_top_level_effects"), (Bool (true))))::((("odir"), (Unset)))::((("prims"), (Unset)))::((("pretype"), (Bool (true))))::((("prims_ref"), (Unset)))::((("print_before_norm"), (Bool (false))))::((("print_bound_var_types"), (Bool (false))))::((("print_effect_args"), (Bool (false))))::((("print_fuels"), (Bool (false))))::((("print_full_names"), (Bool (false))))::((("print_implicits"), (Bool (false))))::((("print_universes"), (Bool (false))))::((("print_z3_statistics"), (Bool (false))))::((("prn"), (Bool (false))))::((("record_hints"), (Bool (false))))::((("reuse_hint_for"), (Unset)))::((("show_signatures"), (List ([]))))::((("silent"), (Bool (false))))::((("smt"), (Unset)))::((("split_cases"), (Int ((Prims.parse_int "0")))))::((("timing"), (Bool (false))))::((("trace_error"), (Bool (false))))::((("unthrottle_inductives"), (Bool (false))))::((("use_eq_at_higher_order"), (Bool (false))))::((("use_hints"), (Bool (false))))::((("no_tactics"), (Bool (false))))::((("verify"), (Bool (true))))::((("verify_all"), (Bool (false))))::((("verify_module"), (List ([]))))::((("warn_default_effects"), (Bool (false))))::((("z3refresh"), (Bool (false))))::((("z3rlimit"), (Int ((Prims.parse_int "5")))))::((("z3rlimit_factor"), (Int ((Prims.parse_int "1")))))::((("z3seed"), (Int ((Prims.parse_int "0")))))::((("z3timeout"), (Int ((Prims.parse_int "5")))))::((("z3cliopt"), (List ([]))))::((("__no_positivity"), (Bool (false))))::[]


let init : Prims.unit  ->  Prims.unit = (fun uu____487 -> (

let o = (peek ())
in ((FStar_Util.smap_clear o);
(FStar_All.pipe_right defaults (FStar_List.iter set_option'));
)))


let clear : Prims.unit  ->  Prims.unit = (fun uu____498 -> (

let o = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_ST.write fstar_options ((o)::[]));
(FStar_ST.write light_off_files []);
(init ());
)))


let _run : Prims.unit = (clear ())


let get_option : Prims.string  ->  option_val = (fun s -> (

let uu____515 = (

let uu____517 = (peek ())
in (FStar_Util.smap_try_find uu____517 s))
in (match (uu____515) with
| None -> begin
(failwith (Prims.strcat "Impossible: option " (Prims.strcat s " not found")))
end
| Some (s1) -> begin
s1
end)))


let lookup_opt = (fun s c -> (c (get_option s)))


let get_admit_smt_queries : Prims.unit  ->  Prims.bool = (fun uu____539 -> (lookup_opt "admit_smt_queries" as_bool))


let get_cardinality : Prims.unit  ->  Prims.string = (fun uu____542 -> (lookup_opt "cardinality" as_string))


let get_codegen : Prims.unit  ->  Prims.string Prims.option = (fun uu____546 -> (lookup_opt "codegen" (as_option as_string)))


let get_codegen_lib : Prims.unit  ->  Prims.string Prims.list = (fun uu____551 -> (lookup_opt "codegen-lib" (as_list as_string)))


let get_debug : Prims.unit  ->  Prims.string Prims.list = (fun uu____556 -> (lookup_opt "debug" (as_list as_string)))


let get_debug_level : Prims.unit  ->  Prims.string Prims.list = (fun uu____561 -> (lookup_opt "debug_level" (as_list as_string)))


let get_dep : Prims.unit  ->  Prims.string Prims.option = (fun uu____566 -> (lookup_opt "dep" (as_option as_string)))


let get_detail_errors : Prims.unit  ->  Prims.bool = (fun uu____570 -> (lookup_opt "detail_errors" as_bool))


let get_doc : Prims.unit  ->  Prims.bool = (fun uu____573 -> (lookup_opt "doc" as_bool))


let get_dump_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____577 -> (lookup_opt "dump_module" (as_list as_string)))


let get_eager_inference : Prims.unit  ->  Prims.bool = (fun uu____581 -> (lookup_opt "eager_inference" as_bool))


let get_explicit_deps : Prims.unit  ->  Prims.bool = (fun uu____584 -> (lookup_opt "explicit_deps" as_bool))


let get_extract_all : Prims.unit  ->  Prims.bool = (fun uu____587 -> (lookup_opt "extract_all" as_bool))


let get_extract_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____591 -> (lookup_opt "extract_module" (as_list as_string)))


let get_extract_namespace : Prims.unit  ->  Prims.string Prims.list = (fun uu____596 -> (lookup_opt "extract_namespace" (as_list as_string)))


let get_fs_typ_app : Prims.unit  ->  Prims.bool = (fun uu____600 -> (lookup_opt "fs_typ_app" as_bool))


let get_fstar_home : Prims.unit  ->  Prims.string Prims.option = (fun uu____604 -> (lookup_opt "fstar_home" (as_option as_string)))


let get_hide_genident_nums : Prims.unit  ->  Prims.bool = (fun uu____608 -> (lookup_opt "hide_genident_nums" as_bool))


let get_hide_uvar_nums : Prims.unit  ->  Prims.bool = (fun uu____611 -> (lookup_opt "hide_uvar_nums" as_bool))


let get_hint_info : Prims.unit  ->  Prims.bool = (fun uu____614 -> (lookup_opt "hint_info" as_bool))


let get_in : Prims.unit  ->  Prims.bool = (fun uu____617 -> (lookup_opt "in" as_bool))


let get_ide : Prims.unit  ->  Prims.bool = (fun uu____620 -> (lookup_opt "ide" as_bool))


let get_include : Prims.unit  ->  Prims.string Prims.list = (fun uu____624 -> (lookup_opt "include" (as_list as_string)))


let get_indent : Prims.unit  ->  Prims.bool = (fun uu____628 -> (lookup_opt "indent" as_bool))


let get_initial_fuel : Prims.unit  ->  Prims.int = (fun uu____631 -> (lookup_opt "initial_fuel" as_int))


let get_initial_ifuel : Prims.unit  ->  Prims.int = (fun uu____634 -> (lookup_opt "initial_ifuel" as_int))


let get_inline_arith : Prims.unit  ->  Prims.bool = (fun uu____637 -> (lookup_opt "inline_arith" as_bool))


let get_lax : Prims.unit  ->  Prims.bool = (fun uu____640 -> (lookup_opt "lax" as_bool))


let get_log_queries : Prims.unit  ->  Prims.bool = (fun uu____643 -> (lookup_opt "log_queries" as_bool))


let get_log_types : Prims.unit  ->  Prims.bool = (fun uu____646 -> (lookup_opt "log_types" as_bool))


let get_max_fuel : Prims.unit  ->  Prims.int = (fun uu____649 -> (lookup_opt "max_fuel" as_int))


let get_max_ifuel : Prims.unit  ->  Prims.int = (fun uu____652 -> (lookup_opt "max_ifuel" as_int))


let get_min_fuel : Prims.unit  ->  Prims.int = (fun uu____655 -> (lookup_opt "min_fuel" as_int))


let get_MLish : Prims.unit  ->  Prims.bool = (fun uu____658 -> (lookup_opt "MLish" as_bool))


let get_n_cores : Prims.unit  ->  Prims.int = (fun uu____661 -> (lookup_opt "n_cores" as_int))


let get_no_default_includes : Prims.unit  ->  Prims.bool = (fun uu____664 -> (lookup_opt "no_default_includes" as_bool))


let get_no_extract : Prims.unit  ->  Prims.string Prims.list = (fun uu____668 -> (lookup_opt "no_extract" (as_list as_string)))


let get_no_location_info : Prims.unit  ->  Prims.bool = (fun uu____672 -> (lookup_opt "no_location_info" as_bool))


let get_warn_top_level_effects : Prims.unit  ->  Prims.bool = (fun uu____675 -> (lookup_opt "no_warn_top_level_effects" as_bool))


let get_odir : Prims.unit  ->  Prims.string Prims.option = (fun uu____679 -> (lookup_opt "odir" (as_option as_string)))


let get_prims : Prims.unit  ->  Prims.string Prims.option = (fun uu____684 -> (lookup_opt "prims" (as_option as_string)))


let get_print_before_norm : Prims.unit  ->  Prims.bool = (fun uu____688 -> (lookup_opt "print_before_norm" as_bool))


let get_print_bound_var_types : Prims.unit  ->  Prims.bool = (fun uu____691 -> (lookup_opt "print_bound_var_types" as_bool))


let get_print_effect_args : Prims.unit  ->  Prims.bool = (fun uu____694 -> (lookup_opt "print_effect_args" as_bool))


let get_print_fuels : Prims.unit  ->  Prims.bool = (fun uu____697 -> (lookup_opt "print_fuels" as_bool))


let get_print_full_names : Prims.unit  ->  Prims.bool = (fun uu____700 -> (lookup_opt "print_full_names" as_bool))


let get_print_implicits : Prims.unit  ->  Prims.bool = (fun uu____703 -> (lookup_opt "print_implicits" as_bool))


let get_print_universes : Prims.unit  ->  Prims.bool = (fun uu____706 -> (lookup_opt "print_universes" as_bool))


let get_print_z3_statistics : Prims.unit  ->  Prims.bool = (fun uu____709 -> (lookup_opt "print_z3_statistics" as_bool))


let get_prn : Prims.unit  ->  Prims.bool = (fun uu____712 -> (lookup_opt "prn" as_bool))


let get_record_hints : Prims.unit  ->  Prims.bool = (fun uu____715 -> (lookup_opt "record_hints" as_bool))


let get_reuse_hint_for : Prims.unit  ->  Prims.string Prims.option = (fun uu____719 -> (lookup_opt "reuse_hint_for" (as_option as_string)))


let get_show_signatures : Prims.unit  ->  Prims.string Prims.list = (fun uu____724 -> (lookup_opt "show_signatures" (as_list as_string)))


let get_silent : Prims.unit  ->  Prims.bool = (fun uu____728 -> (lookup_opt "silent" as_bool))


let get_smt : Prims.unit  ->  Prims.string Prims.option = (fun uu____732 -> (lookup_opt "smt" (as_option as_string)))


let get_split_cases : Prims.unit  ->  Prims.int = (fun uu____736 -> (lookup_opt "split_cases" as_int))


let get_timing : Prims.unit  ->  Prims.bool = (fun uu____739 -> (lookup_opt "timing" as_bool))


let get_trace_error : Prims.unit  ->  Prims.bool = (fun uu____742 -> (lookup_opt "trace_error" as_bool))


let get_unthrottle_inductives : Prims.unit  ->  Prims.bool = (fun uu____745 -> (lookup_opt "unthrottle_inductives" as_bool))


let get_use_eq_at_higher_order : Prims.unit  ->  Prims.bool = (fun uu____748 -> (lookup_opt "use_eq_at_higher_order" as_bool))


let get_use_hints : Prims.unit  ->  Prims.bool = (fun uu____751 -> (lookup_opt "use_hints" as_bool))


let get_use_tactics : Prims.unit  ->  Prims.bool = (fun uu____754 -> (

let uu____755 = (lookup_opt "no_tactics" as_bool)
in (not (uu____755))))


let get_verify_all : Prims.unit  ->  Prims.bool = (fun uu____758 -> (lookup_opt "verify_all" as_bool))


let get_verify_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____762 -> (lookup_opt "verify_module" (as_list as_string)))


let get___temp_no_proj : Prims.unit  ->  Prims.string Prims.list = (fun uu____767 -> (lookup_opt "__temp_no_proj" (as_list as_string)))


let get_version : Prims.unit  ->  Prims.bool = (fun uu____771 -> (lookup_opt "version" as_bool))


let get_warn_default_effects : Prims.unit  ->  Prims.bool = (fun uu____774 -> (lookup_opt "warn_default_effects" as_bool))


let get_z3cliopt : Prims.unit  ->  Prims.string Prims.list = (fun uu____778 -> (lookup_opt "z3cliopt" (as_list as_string)))


let get_z3refresh : Prims.unit  ->  Prims.bool = (fun uu____782 -> (lookup_opt "z3refresh" as_bool))


let get_z3rlimit : Prims.unit  ->  Prims.int = (fun uu____785 -> (lookup_opt "z3rlimit" as_int))


let get_z3rlimit_factor : Prims.unit  ->  Prims.int = (fun uu____788 -> (lookup_opt "z3rlimit_factor" as_int))


let get_z3seed : Prims.unit  ->  Prims.int = (fun uu____791 -> (lookup_opt "z3seed" as_int))


let get_z3timeout : Prims.unit  ->  Prims.int = (fun uu____794 -> (lookup_opt "z3timeout" as_int))


let get_no_positivity : Prims.unit  ->  Prims.bool = (fun uu____797 -> (lookup_opt "__no_positivity" as_bool))


let dlevel : Prims.string  ->  debug_level_t = (fun uu___56_800 -> (match (uu___56_800) with
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
| (Other (_)) | (Low) -> begin
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

let uu____812 = (get_debug_level ())
in (FStar_All.pipe_right uu____812 (FStar_Util.for_some (fun l1 -> (one_debug_level_geq (dlevel l1) l2))))))


let universe_include_path_base_dirs : Prims.string Prims.list = ("/ulib")::("/lib/fstar")::[]


let _version : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _platform : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _compiler : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _date : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let _commit : Prims.string FStar_ST.ref = (FStar_Util.mk_ref "")


let display_version : Prims.unit  ->  Prims.unit = (fun uu____839 -> (

let uu____840 = (

let uu____841 = (FStar_ST.read _version)
in (

let uu____844 = (FStar_ST.read _platform)
in (

let uu____847 = (FStar_ST.read _compiler)
in (

let uu____850 = (FStar_ST.read _date)
in (

let uu____853 = (FStar_ST.read _commit)
in (FStar_Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____841 uu____844 uu____847 uu____850 uu____853))))))
in (FStar_Util.print_string uu____840)))


let display_usage_aux = (fun specs -> ((FStar_Util.print_string "fstar.exe [options] file[s]\n");
(FStar_List.iter (fun uu____883 -> (match (uu____883) with
| (uu____889, flag, p, doc) -> begin
(match (p) with
| FStar_Getopt.ZeroArgs (ig) -> begin
(match ((doc = "")) with
| true -> begin
(

let uu____898 = (

let uu____899 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format1 "  --%s\n" uu____899))
in (FStar_Util.print_string uu____898))
end
| uu____900 -> begin
(

let uu____901 = (

let uu____902 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format2 "  --%s  %s\n" uu____902 doc))
in (FStar_Util.print_string uu____901))
end)
end
| FStar_Getopt.OneArg (uu____903, argname) -> begin
(match ((doc = "")) with
| true -> begin
(

let uu____909 = (

let uu____910 = (FStar_Util.colorize_bold flag)
in (

let uu____911 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format2 "  --%s %s\n" uu____910 uu____911)))
in (FStar_Util.print_string uu____909))
end
| uu____912 -> begin
(

let uu____913 = (

let uu____914 = (FStar_Util.colorize_bold flag)
in (

let uu____915 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format3 "  --%s %s  %s\n" uu____914 uu____915 doc)))
in (FStar_Util.print_string uu____913))
end)
end)
end)) specs);
))


let mk_spec : (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant * Prims.string)  ->  FStar_Getopt.opt = (fun o -> (

let uu____929 = o
in (match (uu____929) with
| (ns, name, arg, desc) -> begin
(

let arg1 = (match (arg) with
| FStar_Getopt.ZeroArgs (f) -> begin
(

let g = (fun uu____950 -> (

let uu____951 = (

let uu____954 = (f ())
in ((name), (uu____954)))
in (set_option' uu____951)))
in FStar_Getopt.ZeroArgs (g))
end
| FStar_Getopt.OneArg (f, d) -> begin
(

let g = (fun x -> (

let uu____965 = (

let uu____968 = (f x)
in ((name), (uu____968)))
in (set_option' uu____965)))
in FStar_Getopt.OneArg (((g), (d))))
end)
in ((ns), (name), (arg1), (desc)))
end)))


let cons_extract_module : Prims.string  ->  option_val = (fun s -> (

let uu____975 = (

let uu____977 = (

let uu____979 = (get_extract_module ())
in ((FStar_String.lowercase s))::uu____979)
in (FStar_All.pipe_right uu____977 (FStar_List.map (fun _0_25 -> String (_0_25)))))
in List (uu____975)))


let cons_extract_namespace : Prims.string  ->  option_val = (fun s -> (

let uu____986 = (

let uu____988 = (

let uu____990 = (get_extract_namespace ())
in ((FStar_String.lowercase s))::uu____990)
in (FStar_All.pipe_right uu____988 (FStar_List.map (fun _0_26 -> String (_0_26)))))
in List (uu____986)))


let add_extract_module : Prims.string  ->  Prims.unit = (fun s -> (

let uu____997 = (cons_extract_module s)
in (set_option "extract_module" uu____997)))


let add_extract_namespace : Prims.string  ->  Prims.unit = (fun s -> (

let uu____1001 = (cons_extract_namespace s)
in (set_option "extract_namespace" uu____1001)))


let cons_verify_module : Prims.string  ->  option_val = (fun s -> (

let uu____1005 = (

let uu____1007 = (

let uu____1009 = (get_verify_module ())
in ((FStar_String.lowercase s))::uu____1009)
in (FStar_All.pipe_right uu____1007 (FStar_List.map (fun _0_27 -> String (_0_27)))))
in List (uu____1005)))


let add_verify_module : Prims.string  ->  Prims.unit = (fun s -> (

let uu____1016 = (cons_verify_module s)
in (set_option "verify_module" uu____1016)))


let rec specs : Prims.unit  ->  FStar_Getopt.opt Prims.list = (fun uu____1026 -> (

let specs1 = (((FStar_Getopt.noshort), ("admit_smt_queries"), (FStar_Getopt.OneArg ((((fun s -> (match ((s = "true")) with
| true -> begin
Bool (true)
end
| uu____1044 -> begin
(match ((s = "false")) with
| true -> begin
Bool (false)
end
| uu____1045 -> begin
(failwith "Invalid argument to --admit_smt_queries")
end)
end))), ("[true|false]")))), ("Admit SMT queries, unsafe! (default \'false\')")))::(((FStar_Getopt.noshort), ("cardinality"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1055 = (validate_cardinality x)
in String (uu____1055)))), ("[off|warn|check]")))), ("Check cardinality constraints on inductive data types (default \'off\')")))::(((FStar_Getopt.noshort), ("codegen"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1065 = (parse_codegen s)
in String (uu____1065)))), ("[OCaml|FSharp|Kremlin]")))), ("Generate code for execution")))::(((FStar_Getopt.noshort), ("codegen-lib"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1075 = (

let uu____1077 = (

let uu____1079 = (get_codegen_lib ())
in (s)::uu____1079)
in (FStar_All.pipe_right uu____1077 (FStar_List.map (fun _0_28 -> String (_0_28)))))
in List (uu____1075)))), ("[namespace]")))), ("External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")))::(((FStar_Getopt.noshort), ("debug"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1092 = (

let uu____1094 = (

let uu____1096 = (get_debug ())
in (x)::uu____1096)
in (FStar_All.pipe_right uu____1094 (FStar_List.map (fun _0_29 -> String (_0_29)))))
in List (uu____1092)))), ("[module name]")))), ("Print lots of debugging information while checking module")))::(((FStar_Getopt.noshort), ("debug_level"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1109 = (

let uu____1111 = (

let uu____1113 = (get_debug_level ())
in (x)::uu____1113)
in (FStar_All.pipe_right uu____1111 (FStar_List.map (fun _0_30 -> String (_0_30)))))
in List (uu____1109)))), ("[Low|Medium|High|Extreme|...]")))), ("Control the verbosity of debugging info")))::(((FStar_Getopt.noshort), ("dep"), (FStar_Getopt.OneArg ((((fun x -> (match (((x = "make") || (x = "graph"))) with
| true -> begin
String (x)
end
| uu____1126 -> begin
(failwith "invalid argument to \'dep\'")
end))), ("[make|graph]")))), ("Output the transitive closure of the dependency graph in a format suitable for the given tool")))::(((FStar_Getopt.noshort), ("detail_errors"), (FStar_Getopt.ZeroArgs ((fun uu____1133 -> Bool (true)))), ("Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")))::(((FStar_Getopt.noshort), ("doc"), (FStar_Getopt.ZeroArgs ((fun uu____1140 -> Bool (true)))), ("Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")))::(((FStar_Getopt.noshort), ("dump_module"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1150 = (

let uu____1152 = (

let uu____1154 = (get_dump_module ())
in (x)::uu____1154)
in (FStar_All.pipe_right uu____1152 (FStar_List.map (fun _0_31 -> String (_0_31)))))
in (FStar_All.pipe_right uu____1150 (fun _0_32 -> List (_0_32)))))), ("[module name]")))), ("")))::(((FStar_Getopt.noshort), ("eager_inference"), (FStar_Getopt.ZeroArgs ((fun uu____1165 -> Bool (true)))), ("Solve all type-inference constraints eagerly; more efficient but at the cost of generality")))::(((FStar_Getopt.noshort), ("explicit_deps"), (FStar_Getopt.ZeroArgs ((fun uu____1172 -> Bool (true)))), ("Do not find dependencies automatically, the user provides them on the command-line")))::(((FStar_Getopt.noshort), ("extract_all"), (FStar_Getopt.ZeroArgs ((fun uu____1179 -> Bool (true)))), ("Discover the complete dependency graph and do not stop at interface boundaries")))::(((FStar_Getopt.noshort), ("extract_module"), (FStar_Getopt.OneArg (((cons_extract_module), ("[module name]")))), ("Only extract the specified modules (instead of the possibly-partial dependency graph)")))::(((FStar_Getopt.noshort), ("extract_namespace"), (FStar_Getopt.OneArg (((cons_extract_namespace), ("[namespace name]")))), ("Only extract modules in the specified namespace")))::(((FStar_Getopt.noshort), ("fstar_home"), (FStar_Getopt.OneArg ((((fun _0_33 -> Path (_0_33))), ("[dir]")))), ("Set the FSTAR_HOME variable to [dir]")))::(((FStar_Getopt.noshort), ("hide_genident_nums"), (FStar_Getopt.ZeroArgs ((fun uu____1210 -> Bool (true)))), ("Don\'t print generated identifier numbers")))::(((FStar_Getopt.noshort), ("hide_uvar_nums"), (FStar_Getopt.ZeroArgs ((fun uu____1217 -> Bool (true)))), ("Don\'t print unification variable numbers")))::(((FStar_Getopt.noshort), ("hint_info"), (FStar_Getopt.ZeroArgs ((fun uu____1224 -> Bool (true)))), ("Print information regarding hints")))::(((FStar_Getopt.noshort), ("in"), (FStar_Getopt.ZeroArgs ((fun uu____1231 -> Bool (true)))), ("Legacy interactive mode; reads input from stdin")))::(((FStar_Getopt.noshort), ("ide"), (FStar_Getopt.ZeroArgs ((fun uu____1238 -> Bool (true)))), ("JSON-based interactive mode for IDEs")))::(((FStar_Getopt.noshort), ("include"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1248 = (

let uu____1250 = (

let uu____1252 = (get_include ())
in (FStar_List.map (fun _0_34 -> String (_0_34)) uu____1252))
in (FStar_List.append uu____1250 ((Path (s))::[])))
in List (uu____1248)))), ("[path]")))), ("A directory in which to search for files included on the command line")))::(((FStar_Getopt.noshort), ("indent"), (FStar_Getopt.ZeroArgs ((fun uu____1260 -> Bool (true)))), ("Parses and outputs the files on the command line")))::(((FStar_Getopt.noshort), ("initial_fuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1270 = (FStar_Util.int_of_string x)
in Int (uu____1270)))), ("[non-negative integer]")))), ("Number of unrolling of recursive functions to try initially (default 2)")))::(((FStar_Getopt.noshort), ("initial_ifuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1280 = (FStar_Util.int_of_string x)
in Int (uu____1280)))), ("[non-negative integer]")))), ("Number of unrolling of inductive datatypes to try at first (default 1)")))::(((FStar_Getopt.noshort), ("inline_arith"), (FStar_Getopt.ZeroArgs ((fun uu____1287 -> Bool (true)))), ("Inline definitions of arithmetic functions in the SMT encoding")))::(((FStar_Getopt.noshort), ("lax"), (FStar_Getopt.ZeroArgs ((fun uu____1294 -> Bool (true)))), ("Run the lax-type checker only (admit all verification conditions)")))::(((FStar_Getopt.noshort), ("log_types"), (FStar_Getopt.ZeroArgs ((fun uu____1301 -> Bool (true)))), ("Print types computed for data/val/let-bindings")))::(((FStar_Getopt.noshort), ("log_queries"), (FStar_Getopt.ZeroArgs ((fun uu____1308 -> Bool (true)))), ("Log the Z3 queries in several queries-*.smt2 files, as we go")))::(((FStar_Getopt.noshort), ("max_fuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1318 = (FStar_Util.int_of_string x)
in Int (uu____1318)))), ("[non-negative integer]")))), ("Number of unrolling of recursive functions to try at most (default 8)")))::(((FStar_Getopt.noshort), ("max_ifuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1328 = (FStar_Util.int_of_string x)
in Int (uu____1328)))), ("[non-negative integer]")))), ("Number of unrolling of inductive datatypes to try at most (default 2)")))::(((FStar_Getopt.noshort), ("min_fuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1338 = (FStar_Util.int_of_string x)
in Int (uu____1338)))), ("[non-negative integer]")))), ("Minimum number of unrolling of recursive functions to try (default 1)")))::(((FStar_Getopt.noshort), ("MLish"), (FStar_Getopt.ZeroArgs ((fun uu____1345 -> Bool (true)))), ("Trigger various specializations for compiling the F* compiler itself (not meant for user code)")))::(((FStar_Getopt.noshort), ("n_cores"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1355 = (FStar_Util.int_of_string x)
in Int (uu____1355)))), ("[positive integer]")))), ("Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")))::(((FStar_Getopt.noshort), ("no_default_includes"), (FStar_Getopt.ZeroArgs ((fun uu____1362 -> Bool (true)))), ("Ignore the default module search paths")))::(((FStar_Getopt.noshort), ("no_extract"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1372 = (

let uu____1374 = (

let uu____1376 = (get_no_extract ())
in (x)::uu____1376)
in (FStar_All.pipe_right uu____1374 (FStar_List.map (fun _0_35 -> String (_0_35)))))
in List (uu____1372)))), ("[module name]")))), ("Do not extract code from this module")))::(((FStar_Getopt.noshort), ("no_location_info"), (FStar_Getopt.ZeroArgs ((fun uu____1386 -> Bool (true)))), ("Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")))::(((FStar_Getopt.noshort), ("odir"), (FStar_Getopt.OneArg ((((fun p -> (

let uu____1396 = (validate_dir p)
in Path (uu____1396)))), ("[dir]")))), ("Place output in directory [dir]")))::(((FStar_Getopt.noshort), ("prims"), (FStar_Getopt.OneArg ((((fun _0_36 -> String (_0_36))), ("file")))), ("")))::(((FStar_Getopt.noshort), ("print_before_norm"), (FStar_Getopt.ZeroArgs ((fun uu____1411 -> Bool (true)))), ("Do not normalize types before printing (for debugging)")))::(((FStar_Getopt.noshort), ("print_bound_var_types"), (FStar_Getopt.ZeroArgs ((fun uu____1418 -> Bool (true)))), ("Print the types of bound variables")))::(((FStar_Getopt.noshort), ("print_effect_args"), (FStar_Getopt.ZeroArgs ((fun uu____1425 -> Bool (true)))), ("Print inferred predicate transformers for all computation types")))::(((FStar_Getopt.noshort), ("print_fuels"), (FStar_Getopt.ZeroArgs ((fun uu____1432 -> Bool (true)))), ("Print the fuel amounts used for each successful query")))::(((FStar_Getopt.noshort), ("print_full_names"), (FStar_Getopt.ZeroArgs ((fun uu____1439 -> Bool (true)))), ("Print full names of variables")))::(((FStar_Getopt.noshort), ("print_implicits"), (FStar_Getopt.ZeroArgs ((fun uu____1446 -> Bool (true)))), ("Print implicit arguments")))::(((FStar_Getopt.noshort), ("print_universes"), (FStar_Getopt.ZeroArgs ((fun uu____1453 -> Bool (true)))), ("Print universes")))::(((FStar_Getopt.noshort), ("print_z3_statistics"), (FStar_Getopt.ZeroArgs ((fun uu____1460 -> Bool (true)))), ("Print Z3 statistics for each SMT query")))::(((FStar_Getopt.noshort), ("prn"), (FStar_Getopt.ZeroArgs ((fun uu____1467 -> Bool (true)))), ("Print full names (deprecated; use --print_full_names instead)")))::(((FStar_Getopt.noshort), ("record_hints"), (FStar_Getopt.ZeroArgs ((fun uu____1474 -> Bool (true)))), ("Record a database of hints for efficient proof replay")))::(((FStar_Getopt.noshort), ("reuse_hint_for"), (FStar_Getopt.OneArg ((((fun _0_37 -> String (_0_37))), ("top-level name in the current module")))), ("Optimistically, attempt using the recorded hint for \'f\' when trying to verify some other term \'g\'")))::(((FStar_Getopt.noshort), ("show_signatures"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1492 = (

let uu____1494 = (

let uu____1496 = (get_show_signatures ())
in (x)::uu____1496)
in (FStar_All.pipe_right uu____1494 (FStar_List.map (fun _0_38 -> String (_0_38)))))
in List (uu____1492)))), ("[module name]")))), ("Show the checked signatures for all top-level symbols in the module")))::(((FStar_Getopt.noshort), ("silent"), (FStar_Getopt.ZeroArgs ((fun uu____1506 -> Bool (true)))), (" ")))::(((FStar_Getopt.noshort), ("smt"), (FStar_Getopt.OneArg ((((fun _0_39 -> Path (_0_39))), ("[path]")))), ("Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)")))::(((FStar_Getopt.noshort), ("split_cases"), (FStar_Getopt.OneArg ((((fun n1 -> (

let uu____1524 = (FStar_Util.int_of_string n1)
in Int (uu____1524)))), ("[positive integer]")))), ("Partition VC of a match into groups of [n] cases")))::(((FStar_Getopt.noshort), ("timing"), (FStar_Getopt.ZeroArgs ((fun uu____1531 -> Bool (true)))), ("Print the time it takes to verify each top-level definition")))::(((FStar_Getopt.noshort), ("trace_error"), (FStar_Getopt.ZeroArgs ((fun uu____1538 -> Bool (true)))), ("Don\'t print an error message; show an exception trace instead")))::(((FStar_Getopt.noshort), ("unthrottle_inductives"), (FStar_Getopt.ZeroArgs ((fun uu____1545 -> Bool (true)))), ("Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")))::(((FStar_Getopt.noshort), ("use_eq_at_higher_order"), (FStar_Getopt.ZeroArgs ((fun uu____1552 -> Bool (true)))), ("Use equality constraints when comparing higher-order types (Temporary)")))::(((FStar_Getopt.noshort), ("use_hints"), (FStar_Getopt.ZeroArgs ((fun uu____1559 -> Bool (true)))), ("Use a previously recorded hints database for proof replay")))::(((FStar_Getopt.noshort), ("no_tactics"), (FStar_Getopt.ZeroArgs ((fun uu____1566 -> Bool (true)))), ("Do not run the tactic engine before discharging a VC")))::(((FStar_Getopt.noshort), ("verify_all"), (FStar_Getopt.ZeroArgs ((fun uu____1573 -> Bool (true)))), ("With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.")))::(((FStar_Getopt.noshort), ("verify_module"), (FStar_Getopt.OneArg (((cons_verify_module), ("[module name]")))), ("Name of the module to verify")))::(((FStar_Getopt.noshort), ("__temp_no_proj"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1591 = (

let uu____1593 = (

let uu____1595 = (get___temp_no_proj ())
in (x)::uu____1595)
in (FStar_All.pipe_right uu____1593 (FStar_List.map (fun _0_40 -> String (_0_40)))))
in List (uu____1591)))), ("[module name]")))), ("Don\'t generate projectors for this module")))::((('v'), ("version"), (FStar_Getopt.ZeroArgs ((fun uu____1605 -> ((display_version ());
(FStar_All.exit (Prims.parse_int "0"));
)))), ("Display version number")))::(((FStar_Getopt.noshort), ("warn_default_effects"), (FStar_Getopt.ZeroArgs ((fun uu____1613 -> Bool (true)))), ("Warn when (a -> b) is desugared to (a -> Tot b)")))::(((FStar_Getopt.noshort), ("z3cliopt"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1623 = (

let uu____1625 = (

let uu____1627 = (get_z3cliopt ())
in (FStar_List.append uu____1627 ((s)::[])))
in (FStar_All.pipe_right uu____1625 (FStar_List.map (fun _0_41 -> String (_0_41)))))
in List (uu____1623)))), ("[option]")))), ("Z3 command line options")))::(((FStar_Getopt.noshort), ("z3refresh"), (FStar_Getopt.ZeroArgs ((fun uu____1637 -> Bool (true)))), ("Restart Z3 after each query; useful for ensuring proof robustness")))::(((FStar_Getopt.noshort), ("z3rlimit"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1647 = (FStar_Util.int_of_string s)
in Int (uu____1647)))), ("[positive integer]")))), ("Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")))::(((FStar_Getopt.noshort), ("z3rlimit_factor"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1657 = (FStar_Util.int_of_string s)
in Int (uu____1657)))), ("[positive integer]")))), ("Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")))::(((FStar_Getopt.noshort), ("z3seed"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1667 = (FStar_Util.int_of_string s)
in Int (uu____1667)))), ("[positive integer]")))), ("Set the Z3 random seed (default 0)")))::(((FStar_Getopt.noshort), ("z3timeout"), (FStar_Getopt.OneArg ((((fun s -> ((FStar_Util.print_string "Warning: z3timeout ignored; use z3rlimit instead\n");
(

let uu____1678 = (FStar_Util.int_of_string s)
in Int (uu____1678));
))), ("[positive integer]")))), ("Set the Z3 per-query (soft) timeout to [t] seconds (default 5)")))::(((FStar_Getopt.noshort), ("__no_positivity"), (FStar_Getopt.ZeroArgs ((fun uu____1685 -> Bool (true)))), ("Don\'t check positivity of inductive types")))::[]
in (

let uu____1691 = (FStar_List.map mk_spec specs1)
in ((('h'), ("help"), (FStar_Getopt.ZeroArgs ((fun x -> ((display_usage_aux specs1);
(FStar_All.exit (Prims.parse_int "0"));
)))), ("Display this information")))::uu____1691)))
and parse_codegen : Prims.string  ->  Prims.string = (fun s -> (match (s) with
| ("Kremlin") | ("OCaml") | ("FSharp") -> begin
s
end
| uu____1712 -> begin
((FStar_Util.print_string "Wrong argument to codegen flag\n");
(

let uu____1715 = (specs ())
in (display_usage_aux uu____1715));
(FStar_All.exit (Prims.parse_int "1"));
)
end))
and validate_cardinality : Prims.string  ->  Prims.string = (fun x -> (match (x) with
| ("warn") | ("check") | ("off") -> begin
x
end
| uu____1723 -> begin
((FStar_Util.print_string "Wrong argument to cardinality flag\n");
(

let uu____1726 = (specs ())
in (display_usage_aux uu____1726));
(FStar_All.exit (Prims.parse_int "1"));
)
end))
and validate_dir : Prims.string  ->  Prims.string = (fun p -> ((FStar_Util.mkdir false p);
p;
))


let docs : Prims.unit  ->  (Prims.string * Prims.string) Prims.list = (fun uu____1740 -> (

let uu____1741 = (specs ())
in (FStar_List.map (fun uu____1755 -> (match (uu____1755) with
| (uu____1763, name, uu____1765, doc) -> begin
((name), (doc))
end)) uu____1741)))


let settable : Prims.string  ->  Prims.bool = (fun uu___57_1771 -> (match (uu___57_1771) with
| ("admit_smt_queries") | ("cardinality") | ("debug") | ("debug_level") | ("detail_errors") | ("eager_inference") | ("hide_genident_nums") | ("hide_uvar_nums") | ("hint_info") | ("initial_fuel") | ("initial_ifuel") | ("inline_arith") | ("lax") | ("log_types") | ("log_queries") | ("max_fuel") | ("max_ifuel") | ("min_fuel") | ("print_before_norm") | ("print_bound_var_types") | ("print_effect_args") | ("print_fuels") | ("print_full_names") | ("print_implicits") | ("print_universes") | ("print_z3_statistics") | ("prn") | ("show_signatures") | ("silent") | ("split_cases") | ("timing") | ("trace_error") | ("unthrottle_inductives") | ("use_eq_at_higher_order") | ("no_tactics") | ("__temp_no_proj") | ("no_warn_top_level_effects") | ("reuse_hint_for") | ("z3rlimit_factor") | ("z3rlimit") | ("z3refresh") -> begin
true
end
| uu____1772 -> begin
false
end))


let resettable : Prims.string  ->  Prims.bool = (fun s -> (((settable s) || (s = "z3timeout")) || (s = "z3seed")))


let all_specs : FStar_Getopt.opt Prims.list = (specs ())


let settable_specs : (FStar_BaseTypes.char * Prims.string * Prims.unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____1795 -> (match (uu____1795) with
| (uu____1801, x, uu____1803, uu____1804) -> begin
(settable x)
end))))


let resettable_specs : (FStar_BaseTypes.char * Prims.string * Prims.unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____1825 -> (match (uu____1825) with
| (uu____1831, x, uu____1833, uu____1834) -> begin
(resettable x)
end))))


let display_usage : Prims.unit  ->  Prims.unit = (fun uu____1839 -> (

let uu____1840 = (specs ())
in (display_usage_aux uu____1840)))


let fstar_home : Prims.unit  ->  Prims.string = (fun uu____1849 -> (

let uu____1850 = (get_fstar_home ())
in (match (uu____1850) with
| None -> begin
(

let x = (FStar_Util.get_exec_dir ())
in (

let x1 = (Prims.strcat x "/..")
in ((set_option' (("fstar_home"), (String (x1))));
x1;
)))
end
| Some (x) -> begin
x
end)))


let set_options : options  ->  Prims.string  ->  FStar_Getopt.parse_cmdline_res = (fun o s -> (

let specs1 = (match (o) with
| Set -> begin
resettable_specs
end
| Reset -> begin
resettable_specs
end
| Restore -> begin
all_specs
end)
in (FStar_Getopt.parse_string specs1 (fun uu____1875 -> ()) s)))


let file_list_ : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let parse_cmd_line : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____1886 -> (

let res = (

let uu____1888 = (specs ())
in (FStar_Getopt.parse_cmdline uu____1888 (fun i -> (

let uu____1891 = (

let uu____1893 = (FStar_ST.read file_list_)
in (FStar_List.append uu____1893 ((i)::[])))
in (FStar_ST.write file_list_ uu____1891)))))
in (

let uu____1901 = (

let uu____1903 = (FStar_ST.read file_list_)
in (FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____1903))
in ((res), (uu____1901)))))


let file_list : Prims.unit  ->  Prims.string Prims.list = (fun uu____1912 -> (FStar_ST.read file_list_))


let restore_cmd_line_options : Prims.bool  ->  FStar_Getopt.parse_cmdline_res = (fun should_clear -> (

let old_verify_module = (get_verify_module ())
in ((match (should_clear) with
| true -> begin
(clear ())
end
| uu____1922 -> begin
(init ())
end);
(

let r = (

let uu____1924 = (specs ())
in (FStar_Getopt.parse_cmdline uu____1924 (fun x -> ())))
in ((

let uu____1928 = (

let uu____1931 = (

let uu____1932 = (FStar_List.map (fun _0_42 -> String (_0_42)) old_verify_module)
in List (uu____1932))
in (("verify_module"), (uu____1931)))
in (set_option' uu____1928));
r;
));
)))


let should_verify : Prims.string  ->  Prims.bool = (fun m -> (

let uu____1937 = (get_lax ())
in (match (uu____1937) with
| true -> begin
false
end
| uu____1938 -> begin
(

let uu____1939 = (get_verify_all ())
in (match (uu____1939) with
| true -> begin
true
end
| uu____1940 -> begin
(

let uu____1941 = (get_verify_module ())
in (match (uu____1941) with
| [] -> begin
(

let uu____1943 = (file_list ())
in (FStar_List.existsML (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let f2 = (

let uu____1948 = (

let uu____1949 = (

let uu____1950 = (

let uu____1951 = (FStar_Util.get_file_extension f1)
in (FStar_String.length uu____1951))
in ((FStar_String.length f1) - uu____1950))
in (uu____1949 - (Prims.parse_int "1")))
in (FStar_String.substring f1 (Prims.parse_int "0") uu____1948))
in ((FStar_String.lowercase f2) = m)))) uu____1943))
end
| l -> begin
(FStar_List.contains (FStar_String.lowercase m) l)
end))
end))
end)))


let dont_gen_projectors : Prims.string  ->  Prims.bool = (fun m -> (

let uu____1961 = (get___temp_no_proj ())
in (FStar_List.contains m uu____1961)))


let should_print_message : Prims.string  ->  Prims.bool = (fun m -> (

let uu____1966 = (should_verify m)
in (match (uu____1966) with
| true -> begin
(m <> "Prims")
end
| uu____1967 -> begin
false
end)))


let include_path : Prims.unit  ->  Prims.string Prims.list = (fun uu____1971 -> (

let uu____1972 = (get_no_default_includes ())
in (match (uu____1972) with
| true -> begin
(get_include ())
end
| uu____1974 -> begin
(

let h = (fstar_home ())
in (

let defs = universe_include_path_base_dirs
in (

let uu____1978 = (

let uu____1980 = (FStar_All.pipe_right defs (FStar_List.map (fun x -> (Prims.strcat h x))))
in (FStar_All.pipe_right uu____1980 (FStar_List.filter FStar_Util.file_exists)))
in (

let uu____1987 = (

let uu____1989 = (get_include ())
in (FStar_List.append uu____1989 ((".")::[])))
in (FStar_List.append uu____1978 uu____1987)))))
end)))


let find_file : Prims.string  ->  Prims.string Prims.option = (fun filename -> (

let uu____1995 = (FStar_Util.is_path_absolute filename)
in (match (uu____1995) with
| true -> begin
(match ((FStar_Util.file_exists filename)) with
| true -> begin
Some (filename)
end
| uu____1998 -> begin
None
end)
end
| uu____1999 -> begin
(

let uu____2000 = (

let uu____2002 = (include_path ())
in (FStar_List.rev uu____2002))
in (FStar_Util.find_map uu____2000 (fun p -> (

let path = (FStar_Util.join_paths p filename)
in (match ((FStar_Util.file_exists path)) with
| true -> begin
Some (path)
end
| uu____2007 -> begin
None
end)))))
end)))


let prims : Prims.unit  ->  Prims.string = (fun uu____2010 -> (

let uu____2011 = (get_prims ())
in (match (uu____2011) with
| None -> begin
(

let filename = "prims.fst"
in (

let uu____2014 = (find_file filename)
in (match (uu____2014) with
| Some (result) -> begin
result
end
| None -> begin
(

let uu____2017 = (

let uu____2018 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in FStar_Util.Failure (uu____2018))
in (Prims.raise uu____2017))
end)))
end
| Some (x) -> begin
x
end)))


let prims_basename : Prims.unit  ->  Prims.string = (fun uu____2022 -> (

let uu____2023 = (prims ())
in (FStar_Util.basename uu____2023)))


let prepend_output_dir : Prims.string  ->  Prims.string = (fun fname -> (

let uu____2027 = (get_odir ())
in (match (uu____2027) with
| None -> begin
fname
end
| Some (x) -> begin
(Prims.strcat x (Prims.strcat "/" fname))
end)))


let __temp_no_proj : Prims.string  ->  Prims.bool = (fun s -> (

let uu____2033 = (get___temp_no_proj ())
in (FStar_All.pipe_right uu____2033 (FStar_List.contains s))))


let admit_smt_queries : Prims.unit  ->  Prims.bool = (fun uu____2038 -> (get_admit_smt_queries ()))


let check_cardinality : Prims.unit  ->  Prims.bool = (fun uu____2041 -> (

let uu____2042 = (get_cardinality ())
in (uu____2042 = "check")))


let codegen : Prims.unit  ->  Prims.string Prims.option = (fun uu____2046 -> (get_codegen ()))


let codegen_libs : Prims.unit  ->  Prims.string Prims.list Prims.list = (fun uu____2051 -> (

let uu____2052 = (get_codegen_lib ())
in (FStar_All.pipe_right uu____2052 (FStar_List.map (fun x -> (FStar_Util.split x "."))))))


let debug_any : Prims.unit  ->  Prims.bool = (fun uu____2061 -> (

let uu____2062 = (get_debug ())
in (uu____2062 <> [])))


let debug_at_level : Prims.string  ->  debug_level_t  ->  Prims.bool = (fun modul level -> (((modul = "") || (

let uu____2071 = (get_debug ())
in (FStar_All.pipe_right uu____2071 (FStar_List.contains modul)))) && (debug_level_geq level)))


let dep : Prims.unit  ->  Prims.string Prims.option = (fun uu____2077 -> (get_dep ()))


let detail_errors : Prims.unit  ->  Prims.bool = (fun uu____2080 -> (get_detail_errors ()))


let doc : Prims.unit  ->  Prims.bool = (fun uu____2083 -> (get_doc ()))


let dump_module : Prims.string  ->  Prims.bool = (fun s -> (

let uu____2087 = (get_dump_module ())
in (FStar_All.pipe_right uu____2087 (FStar_List.contains s))))


let eager_inference : Prims.unit  ->  Prims.bool = (fun uu____2092 -> (get_eager_inference ()))


let explicit_deps : Prims.unit  ->  Prims.bool = (fun uu____2095 -> (get_explicit_deps ()))


let extract_all : Prims.unit  ->  Prims.bool = (fun uu____2098 -> (get_extract_all ()))


let fs_typ_app : Prims.string  ->  Prims.bool = (fun filename -> (

let uu____2102 = (FStar_ST.read light_off_files)
in (FStar_List.contains filename uu____2102)))


let full_context_dependency : Prims.unit  ->  Prims.bool = (fun uu____2109 -> true)


let hide_genident_nums : Prims.unit  ->  Prims.bool = (fun uu____2112 -> (get_hide_genident_nums ()))


let hide_uvar_nums : Prims.unit  ->  Prims.bool = (fun uu____2115 -> (get_hide_uvar_nums ()))


let hint_info : Prims.unit  ->  Prims.bool = (fun uu____2118 -> (get_hint_info ()))


let ide : Prims.unit  ->  Prims.bool = (fun uu____2121 -> (get_ide ()))


let indent : Prims.unit  ->  Prims.bool = (fun uu____2124 -> (get_indent ()))


let initial_fuel : Prims.unit  ->  Prims.int = (fun uu____2127 -> (

let uu____2128 = (get_initial_fuel ())
in (

let uu____2129 = (get_max_fuel ())
in (Prims.min uu____2128 uu____2129))))


let initial_ifuel : Prims.unit  ->  Prims.int = (fun uu____2132 -> (

let uu____2133 = (get_initial_ifuel ())
in (

let uu____2134 = (get_max_ifuel ())
in (Prims.min uu____2133 uu____2134))))


let inline_arith : Prims.unit  ->  Prims.bool = (fun uu____2137 -> (get_inline_arith ()))


let interactive : Prims.unit  ->  Prims.bool = (fun uu____2140 -> ((get_in ()) || (get_ide ())))


let lax : Prims.unit  ->  Prims.bool = (fun uu____2143 -> (get_lax ()))


let legacy_interactive : Prims.unit  ->  Prims.bool = (fun uu____2146 -> (get_in ()))


let log_queries : Prims.unit  ->  Prims.bool = (fun uu____2149 -> (get_log_queries ()))


let log_types : Prims.unit  ->  Prims.bool = (fun uu____2152 -> (get_log_types ()))


let max_fuel : Prims.unit  ->  Prims.int = (fun uu____2155 -> (get_max_fuel ()))


let max_ifuel : Prims.unit  ->  Prims.int = (fun uu____2158 -> (get_max_ifuel ()))


let min_fuel : Prims.unit  ->  Prims.int = (fun uu____2161 -> (get_min_fuel ()))


let ml_ish : Prims.unit  ->  Prims.bool = (fun uu____2164 -> (get_MLish ()))


let set_ml_ish : Prims.unit  ->  Prims.unit = (fun uu____2167 -> (set_option "MLish" (Bool (true))))


let n_cores : Prims.unit  ->  Prims.int = (fun uu____2170 -> (get_n_cores ()))


let no_default_includes : Prims.unit  ->  Prims.bool = (fun uu____2173 -> (get_no_default_includes ()))


let no_extract : Prims.string  ->  Prims.bool = (fun s -> (

let uu____2177 = (get_no_extract ())
in (FStar_All.pipe_right uu____2177 (FStar_List.contains s))))


let no_location_info : Prims.unit  ->  Prims.bool = (fun uu____2182 -> (get_no_location_info ()))


let norm_then_print : Prims.unit  ->  Prims.bool = (fun uu____2185 -> (

let uu____2186 = (get_print_before_norm ())
in (uu____2186 = false)))


let output_dir : Prims.unit  ->  Prims.string Prims.option = (fun uu____2190 -> (get_odir ()))


let print_bound_var_types : Prims.unit  ->  Prims.bool = (fun uu____2193 -> (get_print_bound_var_types ()))


let print_effect_args : Prims.unit  ->  Prims.bool = (fun uu____2196 -> (get_print_effect_args ()))


let print_fuels : Prims.unit  ->  Prims.bool = (fun uu____2199 -> (get_print_fuels ()))


let print_implicits : Prims.unit  ->  Prims.bool = (fun uu____2202 -> (get_print_implicits ()))


let print_real_names : Prims.unit  ->  Prims.bool = (fun uu____2205 -> ((get_prn ()) || (get_print_full_names ())))


let print_universes : Prims.unit  ->  Prims.bool = (fun uu____2208 -> (get_print_universes ()))


let print_z3_statistics : Prims.unit  ->  Prims.bool = (fun uu____2211 -> (get_print_z3_statistics ()))


let record_hints : Prims.unit  ->  Prims.bool = (fun uu____2214 -> (get_record_hints ()))


let reuse_hint_for : Prims.unit  ->  Prims.string Prims.option = (fun uu____2218 -> (get_reuse_hint_for ()))


let silent : Prims.unit  ->  Prims.bool = (fun uu____2221 -> (get_silent ()))


let split_cases : Prims.unit  ->  Prims.int = (fun uu____2224 -> (get_split_cases ()))


let timing : Prims.unit  ->  Prims.bool = (fun uu____2227 -> (get_timing ()))


let trace_error : Prims.unit  ->  Prims.bool = (fun uu____2230 -> (get_trace_error ()))


let unthrottle_inductives : Prims.unit  ->  Prims.bool = (fun uu____2233 -> (get_unthrottle_inductives ()))


let use_eq_at_higher_order : Prims.unit  ->  Prims.bool = (fun uu____2236 -> (get_use_eq_at_higher_order ()))


let use_hints : Prims.unit  ->  Prims.bool = (fun uu____2239 -> (get_use_hints ()))


let use_tactics : Prims.unit  ->  Prims.bool = (fun uu____2242 -> (get_use_tactics ()))


let verify_all : Prims.unit  ->  Prims.bool = (fun uu____2245 -> (get_verify_all ()))


let verify_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____2249 -> (get_verify_module ()))


let warn_cardinality : Prims.unit  ->  Prims.bool = (fun uu____2252 -> (

let uu____2253 = (get_cardinality ())
in (uu____2253 = "warn")))


let warn_default_effects : Prims.unit  ->  Prims.bool = (fun uu____2256 -> (get_warn_default_effects ()))


let warn_top_level_effects : Prims.unit  ->  Prims.bool = (fun uu____2259 -> (get_warn_top_level_effects ()))


let z3_exe : Prims.unit  ->  Prims.string = (fun uu____2262 -> (

let uu____2263 = (get_smt ())
in (match (uu____2263) with
| None -> begin
(FStar_Platform.exe "z3")
end
| Some (s) -> begin
s
end)))


let z3_cliopt : Prims.unit  ->  Prims.string Prims.list = (fun uu____2269 -> (get_z3cliopt ()))


let z3_refresh : Prims.unit  ->  Prims.bool = (fun uu____2272 -> (get_z3refresh ()))


let z3_rlimit : Prims.unit  ->  Prims.int = (fun uu____2275 -> (get_z3rlimit ()))


let z3_rlimit_factor : Prims.unit  ->  Prims.int = (fun uu____2278 -> (get_z3rlimit_factor ()))


let z3_seed : Prims.unit  ->  Prims.int = (fun uu____2281 -> (get_z3seed ()))


let z3_timeout : Prims.unit  ->  Prims.int = (fun uu____2284 -> (get_z3timeout ()))


let no_positivity : Prims.unit  ->  Prims.bool = (fun uu____2287 -> (get_no_positivity ()))


let should_extract : Prims.string  ->  Prims.bool = (fun m -> ((

let uu____2291 = (no_extract m)
in (not (uu____2291))) && ((extract_all ()) || (

let uu____2292 = (get_extract_module ())
in (match (uu____2292) with
| [] -> begin
(

let uu____2294 = (get_extract_namespace ())
in (match (uu____2294) with
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




