
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
| Int of Prims.int
| List of option_val Prims.list
| Unset


let uu___is_Bool : option_val  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Bool (_0) -> begin
true
end
| uu____49 -> begin
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
| uu____61 -> begin
false
end))


let __proj__String__item___0 : option_val  ->  Prims.string = (fun projectee -> (match (projectee) with
| String (_0) -> begin
_0
end))


let uu___is_Int : option_val  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int (_0) -> begin
true
end
| uu____73 -> begin
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
| uu____86 -> begin
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
| uu____100 -> begin
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
| uu____104 -> begin
false
end))


let uu___is_Reset : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reset -> begin
true
end
| uu____108 -> begin
false
end))


let uu___is_Restore : options  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Restore -> begin
true
end
| uu____112 -> begin
false
end))


let __unit_tests__ : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let __unit_tests : Prims.unit  ->  Prims.bool = (fun uu____118 -> (FStar_ST.read __unit_tests__))


let __set_unit_tests : Prims.unit  ->  Prims.unit = (fun uu____123 -> (FStar_ST.write __unit_tests__ true))


let __clear_unit_tests : Prims.unit  ->  Prims.unit = (fun uu____128 -> (FStar_ST.write __unit_tests__ false))


let as_bool : option_val  ->  Prims.bool = (fun uu___43_133 -> (match (uu___43_133) with
| Bool (b) -> begin
b
end
| uu____135 -> begin
(failwith "Impos: expected Bool")
end))


let as_int : option_val  ->  Prims.int = (fun uu___44_138 -> (match (uu___44_138) with
| Int (b) -> begin
b
end
| uu____140 -> begin
(failwith "Impos: expected Int")
end))


let as_string : option_val  ->  Prims.string = (fun uu___45_143 -> (match (uu___45_143) with
| String (b) -> begin
b
end
| uu____145 -> begin
(failwith "Impos: expected String")
end))


let as_list = (fun as_t uu___46_161 -> (match (uu___46_161) with
| List (ts) -> begin
(FStar_All.pipe_right ts (FStar_List.map as_t))
end
| uu____168 -> begin
(failwith "Impos: expected List")
end))


let as_option = (fun as_t uu___47_185 -> (match (uu___47_185) with
| Unset -> begin
None
end
| v -> begin
(

let uu____189 = (as_t v)
in Some (uu____189))
end))


let fstar_options : option_val FStar_Util.smap Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let peek : Prims.unit  ->  option_val FStar_Util.smap = (fun uu____201 -> (

let uu____202 = (FStar_ST.read fstar_options)
in (FStar_List.hd uu____202)))


let pop : Prims.unit  ->  Prims.unit = (fun uu____212 -> (

let uu____213 = (FStar_ST.read fstar_options)
in (match (uu____213) with
| ([]) | ((_)::[]) -> begin
(failwith "TOO MANY POPS!")
end
| (uu____224)::tl -> begin
(FStar_ST.write fstar_options tl)
end)))


let push : Prims.unit  ->  Prims.unit = (fun uu____236 -> (

let uu____237 = (

let uu____240 = (

let uu____242 = (peek ())
in (FStar_Util.smap_copy uu____242))
in (

let uu____244 = (FStar_ST.read fstar_options)
in (uu____240)::uu____244))
in (FStar_ST.write fstar_options uu____237)))


let set_option : Prims.string  ->  option_val  ->  Prims.unit = (fun k v -> (

let uu____262 = (peek ())
in (FStar_Util.smap_add uu____262 k v)))


let set_option' : (Prims.string * option_val)  ->  Prims.unit = (fun uu____268 -> (match (uu____268) with
| (k, v) -> begin
(set_option k v)
end))


let light_off_files : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let add_light_off_file : Prims.string  ->  Prims.unit = (fun filename -> (

let uu____281 = (

let uu____283 = (FStar_ST.read light_off_files)
in (filename)::uu____283)
in (FStar_ST.write light_off_files uu____281)))


let init : Prims.unit  ->  Prims.unit = (fun uu____293 -> (

let vals = ((("__temp_no_proj"), (List ([]))))::((("_fstar_home"), (String (""))))::((("_include_path"), (List ([]))))::((("admit_smt_queries"), (Bool (false))))::((("cardinality"), (String ("off"))))::((("codegen"), (Unset)))::((("codegen-lib"), (List ([]))))::((("debug"), (List ([]))))::((("debug_level"), (List ([]))))::((("dep"), (Unset)))::((("detail_errors"), (Bool (false))))::((("doc"), (Bool (false))))::((("dump_module"), (List ([]))))::((("eager_inference"), (Bool (false))))::((("explicit_deps"), (Bool (false))))::((("extract_all"), (Bool (false))))::((("extract_module"), (List ([]))))::((("extract_namespace"), (List ([]))))::((("fs_typ_app"), (Bool (false))))::((("fsi"), (Bool (false))))::((("fstar_home"), (Unset)))::((("full_context_dependency"), (Bool (true))))::((("hide_genident_nums"), (Bool (false))))::((("hide_uvar_nums"), (Bool (false))))::((("hint_info"), (Bool (false))))::((("in"), (Bool (false))))::((("include"), (List ([]))))::((("indent"), (Bool (false))))::((("initial_fuel"), (Int ((Prims.parse_int "2")))))::((("initial_ifuel"), (Int ((Prims.parse_int "1")))))::((("inline_arith"), (Bool (false))))::((("lax"), (Bool (false))))::((("log_queries"), (Bool (false))))::((("log_types"), (Bool (false))))::((("max_fuel"), (Int ((Prims.parse_int "8")))))::((("max_ifuel"), (Int ((Prims.parse_int "2")))))::((("min_fuel"), (Int ((Prims.parse_int "1")))))::((("MLish"), (Bool (false))))::((("n_cores"), (Int ((Prims.parse_int "1")))))::((("no_default_includes"), (Bool (false))))::((("no_extract"), (List ([]))))::((("no_location_info"), (Bool (false))))::((("no_warn_top_level_effects"), (Bool (true))))::((("odir"), (Unset)))::((("prims"), (Unset)))::((("pretype"), (Bool (true))))::((("prims_ref"), (Unset)))::((("print_before_norm"), (Bool (false))))::((("print_bound_var_types"), (Bool (false))))::((("print_effect_args"), (Bool (false))))::((("print_fuels"), (Bool (false))))::((("print_implicits"), (Bool (false))))::((("print_universes"), (Bool (false))))::((("print_z3_statistics"), (Bool (false))))::((("prn"), (Bool (false))))::((("record_hints"), (Bool (false))))::((("reuse_hint_for"), (Unset)))::((("show_signatures"), (List ([]))))::((("silent"), (Bool (false))))::((("smt"), (Unset)))::((("split_cases"), (Int ((Prims.parse_int "0")))))::((("timing"), (Bool (false))))::((("trace_error"), (Bool (false))))::((("unthrottle_inductives"), (Bool (false))))::((("use_eq_at_higher_order"), (Bool (false))))::((("use_hints"), (Bool (false))))::((("verify"), (Bool (true))))::((("verify_all"), (Bool (false))))::((("verify_module"), (List ([]))))::((("warn_default_effects"), (Bool (false))))::((("z3refresh"), (Bool (false))))::((("z3rlimit"), (Int ((Prims.parse_int "5")))))::((("z3seed"), (Int ((Prims.parse_int "0")))))::((("z3timeout"), (Int ((Prims.parse_int "5")))))::((("z3cliopt"), (List ([]))))::((("__no_positivity"), (Bool (false))))::[]
in (

let o = (peek ())
in ((FStar_Util.smap_clear o);
(FStar_All.pipe_right vals (FStar_List.iter set_option'));
))))


let clear : Prims.unit  ->  Prims.unit = (fun uu____462 -> (

let o = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_ST.write fstar_options ((o)::[]));
(FStar_ST.write light_off_files []);
(init ());
)))


let _run : Prims.unit = (clear ())


let lookup_opt = (fun s c -> (

let uu____493 = (

let uu____495 = (peek ())
in (FStar_Util.smap_try_find uu____495 s))
in (match (uu____493) with
| None -> begin
(failwith (Prims.strcat "Impossible: option " (Prims.strcat s " not found")))
end
| Some (s) -> begin
(c s)
end)))


let get_admit_smt_queries : Prims.unit  ->  Prims.bool = (fun uu____500 -> (lookup_opt "admit_smt_queries" as_bool))


let get_cardinality : Prims.unit  ->  Prims.string = (fun uu____503 -> (lookup_opt "cardinality" as_string))


let get_codegen : Prims.unit  ->  Prims.string Prims.option = (fun uu____507 -> (lookup_opt "codegen" (as_option as_string)))


let get_codegen_lib : Prims.unit  ->  Prims.string Prims.list = (fun uu____512 -> (lookup_opt "codegen-lib" (as_list as_string)))


let get_debug : Prims.unit  ->  Prims.string Prims.list = (fun uu____517 -> (lookup_opt "debug" (as_list as_string)))


let get_debug_level : Prims.unit  ->  Prims.string Prims.list = (fun uu____522 -> (lookup_opt "debug_level" (as_list as_string)))


let get_dep : Prims.unit  ->  Prims.string Prims.option = (fun uu____527 -> (lookup_opt "dep" (as_option as_string)))


let get_detail_errors : Prims.unit  ->  Prims.bool = (fun uu____531 -> (lookup_opt "detail_errors" as_bool))


let get_doc : Prims.unit  ->  Prims.bool = (fun uu____534 -> (lookup_opt "doc" as_bool))


let get_dump_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____538 -> (lookup_opt "dump_module" (as_list as_string)))


let get_eager_inference : Prims.unit  ->  Prims.bool = (fun uu____542 -> (lookup_opt "eager_inference" as_bool))


let get_explicit_deps : Prims.unit  ->  Prims.bool = (fun uu____545 -> (lookup_opt "explicit_deps" as_bool))


let get_extract_all : Prims.unit  ->  Prims.bool = (fun uu____548 -> (lookup_opt "extract_all" as_bool))


let get_extract_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____552 -> (lookup_opt "extract_module" (as_list as_string)))


let get_extract_namespace : Prims.unit  ->  Prims.string Prims.list = (fun uu____557 -> (lookup_opt "extract_namespace" (as_list as_string)))


let get_fs_typ_app : Prims.unit  ->  Prims.bool = (fun uu____561 -> (lookup_opt "fs_typ_app" as_bool))


let get_fstar_home : Prims.unit  ->  Prims.string Prims.option = (fun uu____565 -> (lookup_opt "fstar_home" (as_option as_string)))


let get_hide_genident_nums : Prims.unit  ->  Prims.bool = (fun uu____569 -> (lookup_opt "hide_genident_nums" as_bool))


let get_hide_uvar_nums : Prims.unit  ->  Prims.bool = (fun uu____572 -> (lookup_opt "hide_uvar_nums" as_bool))


let get_hint_info : Prims.unit  ->  Prims.bool = (fun uu____575 -> (lookup_opt "hint_info" as_bool))


let get_in : Prims.unit  ->  Prims.bool = (fun uu____578 -> (lookup_opt "in" as_bool))


let get_include : Prims.unit  ->  Prims.string Prims.list = (fun uu____582 -> (lookup_opt "include" (as_list as_string)))


let get_indent : Prims.unit  ->  Prims.bool = (fun uu____586 -> (lookup_opt "indent" as_bool))


let get_initial_fuel : Prims.unit  ->  Prims.int = (fun uu____589 -> (lookup_opt "initial_fuel" as_int))


let get_initial_ifuel : Prims.unit  ->  Prims.int = (fun uu____592 -> (lookup_opt "initial_ifuel" as_int))


let get_inline_arith : Prims.unit  ->  Prims.bool = (fun uu____595 -> (lookup_opt "inline_arith" as_bool))


let get_lax : Prims.unit  ->  Prims.bool = (fun uu____598 -> (lookup_opt "lax" as_bool))


let get_log_queries : Prims.unit  ->  Prims.bool = (fun uu____601 -> (lookup_opt "log_queries" as_bool))


let get_log_types : Prims.unit  ->  Prims.bool = (fun uu____604 -> (lookup_opt "log_types" as_bool))


let get_max_fuel : Prims.unit  ->  Prims.int = (fun uu____607 -> (lookup_opt "max_fuel" as_int))


let get_max_ifuel : Prims.unit  ->  Prims.int = (fun uu____610 -> (lookup_opt "max_ifuel" as_int))


let get_min_fuel : Prims.unit  ->  Prims.int = (fun uu____613 -> (lookup_opt "min_fuel" as_int))


let get_MLish : Prims.unit  ->  Prims.bool = (fun uu____616 -> (lookup_opt "MLish" as_bool))


let get_n_cores : Prims.unit  ->  Prims.int = (fun uu____619 -> (lookup_opt "n_cores" as_int))


let get_no_default_includes : Prims.unit  ->  Prims.bool = (fun uu____622 -> (lookup_opt "no_default_includes" as_bool))


let get_no_extract : Prims.unit  ->  Prims.string Prims.list = (fun uu____626 -> (lookup_opt "no_extract" (as_list as_string)))


let get_no_location_info : Prims.unit  ->  Prims.bool = (fun uu____630 -> (lookup_opt "no_location_info" as_bool))


let get_warn_top_level_effects : Prims.unit  ->  Prims.bool = (fun uu____633 -> (lookup_opt "no_warn_top_level_effects" as_bool))


let get_odir : Prims.unit  ->  Prims.string Prims.option = (fun uu____637 -> (lookup_opt "odir" (as_option as_string)))


let get_prims : Prims.unit  ->  Prims.string Prims.option = (fun uu____642 -> (lookup_opt "prims" (as_option as_string)))


let get_print_before_norm : Prims.unit  ->  Prims.bool = (fun uu____646 -> (lookup_opt "print_before_norm" as_bool))


let get_print_bound_var_types : Prims.unit  ->  Prims.bool = (fun uu____649 -> (lookup_opt "print_bound_var_types" as_bool))


let get_print_effect_args : Prims.unit  ->  Prims.bool = (fun uu____652 -> (lookup_opt "print_effect_args" as_bool))


let get_print_fuels : Prims.unit  ->  Prims.bool = (fun uu____655 -> (lookup_opt "print_fuels" as_bool))


let get_print_implicits : Prims.unit  ->  Prims.bool = (fun uu____658 -> (lookup_opt "print_implicits" as_bool))


let get_print_universes : Prims.unit  ->  Prims.bool = (fun uu____661 -> (lookup_opt "print_universes" as_bool))


let get_print_z3_statistics : Prims.unit  ->  Prims.bool = (fun uu____664 -> (lookup_opt "print_z3_statistics" as_bool))


let get_prn : Prims.unit  ->  Prims.bool = (fun uu____667 -> (lookup_opt "prn" as_bool))


let get_record_hints : Prims.unit  ->  Prims.bool = (fun uu____670 -> (lookup_opt "record_hints" as_bool))


let get_reuse_hint_for : Prims.unit  ->  Prims.string Prims.option = (fun uu____674 -> (lookup_opt "reuse_hint_for" (as_option as_string)))


let get_show_signatures : Prims.unit  ->  Prims.string Prims.list = (fun uu____679 -> (lookup_opt "show_signatures" (as_list as_string)))


let get_silent : Prims.unit  ->  Prims.bool = (fun uu____683 -> (lookup_opt "silent" as_bool))


let get_smt : Prims.unit  ->  Prims.string Prims.option = (fun uu____687 -> (lookup_opt "smt" (as_option as_string)))


let get_split_cases : Prims.unit  ->  Prims.int = (fun uu____691 -> (lookup_opt "split_cases" as_int))


let get_timing : Prims.unit  ->  Prims.bool = (fun uu____694 -> (lookup_opt "timing" as_bool))


let get_trace_error : Prims.unit  ->  Prims.bool = (fun uu____697 -> (lookup_opt "trace_error" as_bool))


let get_unthrottle_inductives : Prims.unit  ->  Prims.bool = (fun uu____700 -> (lookup_opt "unthrottle_inductives" as_bool))


let get_use_eq_at_higher_order : Prims.unit  ->  Prims.bool = (fun uu____703 -> (lookup_opt "use_eq_at_higher_order" as_bool))


let get_use_hints : Prims.unit  ->  Prims.bool = (fun uu____706 -> (lookup_opt "use_hints" as_bool))


let get_verify_all : Prims.unit  ->  Prims.bool = (fun uu____709 -> (lookup_opt "verify_all" as_bool))


let get_verify_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____713 -> (lookup_opt "verify_module" (as_list as_string)))


let get___temp_no_proj : Prims.unit  ->  Prims.string Prims.list = (fun uu____718 -> (lookup_opt "__temp_no_proj" (as_list as_string)))


let get_version : Prims.unit  ->  Prims.bool = (fun uu____722 -> (lookup_opt "version" as_bool))


let get_warn_default_effects : Prims.unit  ->  Prims.bool = (fun uu____725 -> (lookup_opt "warn_default_effects" as_bool))


let get_z3cliopt : Prims.unit  ->  Prims.string Prims.list = (fun uu____729 -> (lookup_opt "z3cliopt" (as_list as_string)))


let get_z3refresh : Prims.unit  ->  Prims.bool = (fun uu____733 -> (lookup_opt "z3refresh" as_bool))


let get_z3rlimit : Prims.unit  ->  Prims.int = (fun uu____736 -> (lookup_opt "z3rlimit" as_int))


let get_z3seed : Prims.unit  ->  Prims.int = (fun uu____739 -> (lookup_opt "z3seed" as_int))


let get_z3timeout : Prims.unit  ->  Prims.int = (fun uu____742 -> (lookup_opt "z3timeout" as_int))


let get_no_positivity : Prims.unit  ->  Prims.bool = (fun uu____745 -> (lookup_opt "__no_positivity" as_bool))


let dlevel : Prims.string  ->  debug_level_t = (fun uu___48_748 -> (match (uu___48_748) with
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

let uu____760 = (get_debug_level ())
in (FStar_All.pipe_right uu____760 (FStar_Util.for_some (fun l1 -> (one_debug_level_geq (dlevel l1) l2))))))


let include_path_base_dirs : Prims.string Prims.list = ("/lib")::("/lib/fstar")::[]


let universe_include_path_base_dirs : Prims.string Prims.list = ("/ulib")::("/lib/fstar")::[]


let display_version : Prims.unit  ->  Prims.unit = (fun uu____768 -> (

let uu____769 = (FStar_Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" FStar_Version.version FStar_Version.platform FStar_Version.compiler FStar_Version.date FStar_Version.commit)
in (FStar_Util.print_string uu____769)))


let display_usage_aux = (fun specs -> ((FStar_Util.print_string "fstar.exe [options] file[s]\n");
(FStar_List.iter (fun uu____797 -> (match (uu____797) with
| (uu____803, flag, p, doc) -> begin
(match (p) with
| FStar_Getopt.ZeroArgs (ig) -> begin
(match ((doc = "")) with
| true -> begin
(

let uu____812 = (

let uu____813 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format1 "  --%s\n" uu____813))
in (FStar_Util.print_string uu____812))
end
| uu____814 -> begin
(

let uu____815 = (

let uu____816 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format2 "  --%s  %s\n" uu____816 doc))
in (FStar_Util.print_string uu____815))
end)
end
| FStar_Getopt.OneArg (uu____817, argname) -> begin
(match ((doc = "")) with
| true -> begin
(

let uu____823 = (

let uu____824 = (FStar_Util.colorize_bold flag)
in (

let uu____825 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format2 "  --%s %s\n" uu____824 uu____825)))
in (FStar_Util.print_string uu____823))
end
| uu____826 -> begin
(

let uu____827 = (

let uu____828 = (FStar_Util.colorize_bold flag)
in (

let uu____829 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format3 "  --%s %s  %s\n" uu____828 uu____829 doc)))
in (FStar_Util.print_string uu____827))
end)
end)
end)) specs);
))


let mk_spec : (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant * Prims.string)  ->  FStar_Getopt.opt = (fun o -> (

let uu____843 = o
in (match (uu____843) with
| (ns, name, arg, desc) -> begin
(

let arg = (match (arg) with
| FStar_Getopt.ZeroArgs (f) -> begin
(

let g = (fun uu____864 -> (

let uu____865 = (

let uu____868 = (f ())
in ((name), (uu____868)))
in (set_option' uu____865)))
in FStar_Getopt.ZeroArgs (g))
end
| FStar_Getopt.OneArg (f, d) -> begin
(

let g = (fun x -> (

let uu____879 = (

let uu____882 = (f x)
in ((name), (uu____882)))
in (set_option' uu____879)))
in FStar_Getopt.OneArg (((g), (d))))
end)
in ((ns), (name), (arg), (desc)))
end)))


let cons_extract_module : Prims.string  ->  option_val = (fun s -> (

let uu____889 = (

let uu____891 = (

let uu____893 = (get_extract_module ())
in ((FStar_String.lowercase s))::uu____893)
in (FStar_All.pipe_right uu____891 (FStar_List.map (fun _0_25 -> String (_0_25)))))
in List (uu____889)))


let cons_extract_namespace : Prims.string  ->  option_val = (fun s -> (

let uu____900 = (

let uu____902 = (

let uu____904 = (get_extract_namespace ())
in ((FStar_String.lowercase s))::uu____904)
in (FStar_All.pipe_right uu____902 (FStar_List.map (fun _0_26 -> String (_0_26)))))
in List (uu____900)))


let add_extract_module : Prims.string  ->  Prims.unit = (fun s -> (

let uu____911 = (cons_extract_module s)
in (set_option "extract_module" uu____911)))


let add_extract_namespace : Prims.string  ->  Prims.unit = (fun s -> (

let uu____915 = (cons_extract_namespace s)
in (set_option "extract_namespace" uu____915)))


let cons_verify_module : Prims.string  ->  option_val = (fun s -> (

let uu____919 = (

let uu____921 = (

let uu____923 = (get_verify_module ())
in ((FStar_String.lowercase s))::uu____923)
in (FStar_All.pipe_right uu____921 (FStar_List.map (fun _0_27 -> String (_0_27)))))
in List (uu____919)))


let add_verify_module : Prims.string  ->  Prims.unit = (fun s -> (

let uu____930 = (cons_verify_module s)
in (set_option "verify_module" uu____930)))


let rec specs : Prims.unit  ->  FStar_Getopt.opt Prims.list = (fun uu____938 -> (

let specs = (((FStar_Getopt.noshort), ("admit_smt_queries"), (FStar_Getopt.OneArg ((((fun s -> (match ((s = "true")) with
| true -> begin
Bool (true)
end
| uu____956 -> begin
(match ((s = "false")) with
| true -> begin
Bool (false)
end
| uu____957 -> begin
(failwith "Invalid argument to --admit_smt_queries")
end)
end))), ("[true|false]")))), ("Admit SMT queries, unsafe! (default \'false\')")))::(((FStar_Getopt.noshort), ("cardinality"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____967 = (validate_cardinality x)
in String (uu____967)))), ("[off|warn|check]")))), ("Check cardinality constraints on inductive data types (default \'off\')")))::(((FStar_Getopt.noshort), ("codegen"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____977 = (parse_codegen s)
in String (uu____977)))), ("[OCaml|FSharp|Kremlin]")))), ("Generate code for execution")))::(((FStar_Getopt.noshort), ("codegen-lib"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____987 = (

let uu____989 = (

let uu____991 = (get_codegen_lib ())
in (s)::uu____991)
in (FStar_All.pipe_right uu____989 (FStar_List.map (fun _0_28 -> String (_0_28)))))
in List (uu____987)))), ("[namespace]")))), ("External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")))::(((FStar_Getopt.noshort), ("debug"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1004 = (

let uu____1006 = (

let uu____1008 = (get_debug ())
in (x)::uu____1008)
in (FStar_All.pipe_right uu____1006 (FStar_List.map (fun _0_29 -> String (_0_29)))))
in List (uu____1004)))), ("[module name]")))), ("Print lots of debugging information while checking module")))::(((FStar_Getopt.noshort), ("debug_level"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1021 = (

let uu____1023 = (

let uu____1025 = (get_debug_level ())
in (x)::uu____1025)
in (FStar_All.pipe_right uu____1023 (FStar_List.map (fun _0_30 -> String (_0_30)))))
in List (uu____1021)))), ("[Low|Medium|High|Extreme|...]")))), ("Control the verbosity of debugging info")))::(((FStar_Getopt.noshort), ("dep"), (FStar_Getopt.OneArg ((((fun x -> (match (((x = "make") || (x = "graph"))) with
| true -> begin
String (x)
end
| uu____1038 -> begin
(failwith "invalid argument to \'dep\'")
end))), ("[make|graph]")))), ("Output the transitive closure of the dependency graph in a format suitable for the given tool")))::(((FStar_Getopt.noshort), ("detail_errors"), (FStar_Getopt.ZeroArgs ((fun uu____1045 -> Bool (true)))), ("Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")))::(((FStar_Getopt.noshort), ("doc"), (FStar_Getopt.ZeroArgs ((fun uu____1052 -> Bool (true)))), ("Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")))::(((FStar_Getopt.noshort), ("dump_module"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1062 = (

let uu____1064 = (

let uu____1066 = (get_dump_module ())
in (x)::uu____1066)
in (FStar_All.pipe_right uu____1064 (FStar_List.map (fun _0_31 -> String (_0_31)))))
in (FStar_All.pipe_right uu____1062 (fun _0_32 -> List (_0_32)))))), ("[module name]")))), ("")))::(((FStar_Getopt.noshort), ("eager_inference"), (FStar_Getopt.ZeroArgs ((fun uu____1077 -> Bool (true)))), ("Solve all type-inference constraints eagerly; more efficient but at the cost of generality")))::(((FStar_Getopt.noshort), ("explicit_deps"), (FStar_Getopt.ZeroArgs ((fun uu____1084 -> Bool (true)))), ("Do not find dependencies automatically, the user provides them on the command-line")))::(((FStar_Getopt.noshort), ("extract_all"), (FStar_Getopt.ZeroArgs ((fun uu____1091 -> Bool (true)))), ("Discover the complete dependency graph and do not stop at interface boundaries")))::(((FStar_Getopt.noshort), ("extract_module"), (FStar_Getopt.OneArg (((cons_extract_module), ("[module name]")))), ("Only extract the specified modules (instead of the possibly-partial dependency graph)")))::(((FStar_Getopt.noshort), ("extract_namespace"), (FStar_Getopt.OneArg (((cons_extract_namespace), ("[namespace name]")))), ("Only extract modules in the specified namespace")))::(((FStar_Getopt.noshort), ("fstar_home"), (FStar_Getopt.OneArg ((((fun _0_33 -> String (_0_33))), ("[dir]")))), ("Set the FSTAR_HOME variable to [dir]")))::(((FStar_Getopt.noshort), ("hide_genident_nums"), (FStar_Getopt.ZeroArgs ((fun uu____1122 -> Bool (true)))), ("Don\'t print generated identifier numbers")))::(((FStar_Getopt.noshort), ("hide_uvar_nums"), (FStar_Getopt.ZeroArgs ((fun uu____1129 -> Bool (true)))), ("Don\'t print unification variable numbers")))::(((FStar_Getopt.noshort), ("hint_info"), (FStar_Getopt.ZeroArgs ((fun uu____1136 -> Bool (true)))), ("Print information regarding hints")))::(((FStar_Getopt.noshort), ("in"), (FStar_Getopt.ZeroArgs ((fun uu____1143 -> Bool (true)))), ("Interactive mode; reads input from stdin")))::(((FStar_Getopt.noshort), ("include"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1153 = (

let uu____1155 = (

let uu____1157 = (get_include ())
in (FStar_List.append uu____1157 ((s)::[])))
in (FStar_All.pipe_right uu____1155 (FStar_List.map (fun _0_34 -> String (_0_34)))))
in List (uu____1153)))), ("[path]")))), ("A directory in which to search for files included on the command line")))::(((FStar_Getopt.noshort), ("indent"), (FStar_Getopt.ZeroArgs ((fun uu____1167 -> Bool (true)))), ("Parses and outputs the files on the command line")))::(((FStar_Getopt.noshort), ("initial_fuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1177 = (FStar_Util.int_of_string x)
in Int (uu____1177)))), ("[non-negative integer]")))), ("Number of unrolling of recursive functions to try initially (default 2)")))::(((FStar_Getopt.noshort), ("initial_ifuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1187 = (FStar_Util.int_of_string x)
in Int (uu____1187)))), ("[non-negative integer]")))), ("Number of unrolling of inductive datatypes to try at first (default 1)")))::(((FStar_Getopt.noshort), ("inline_arith"), (FStar_Getopt.ZeroArgs ((fun uu____1194 -> Bool (true)))), ("Inline definitions of arithmetic functions in the SMT encoding")))::(((FStar_Getopt.noshort), ("lax"), (FStar_Getopt.ZeroArgs ((fun uu____1201 -> Bool (true)))), ("Run the lax-type checker only (admit all verification conditions)")))::(((FStar_Getopt.noshort), ("log_types"), (FStar_Getopt.ZeroArgs ((fun uu____1208 -> Bool (true)))), ("Print types computed for data/val/let-bindings")))::(((FStar_Getopt.noshort), ("log_queries"), (FStar_Getopt.ZeroArgs ((fun uu____1215 -> Bool (true)))), ("Log the Z3 queries in several queries-*.smt2 files, as we go")))::(((FStar_Getopt.noshort), ("max_fuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1225 = (FStar_Util.int_of_string x)
in Int (uu____1225)))), ("[non-negative integer]")))), ("Number of unrolling of recursive functions to try at most (default 8)")))::(((FStar_Getopt.noshort), ("max_ifuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1235 = (FStar_Util.int_of_string x)
in Int (uu____1235)))), ("[non-negative integer]")))), ("Number of unrolling of inductive datatypes to try at most (default 2)")))::(((FStar_Getopt.noshort), ("min_fuel"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1245 = (FStar_Util.int_of_string x)
in Int (uu____1245)))), ("[non-negative integer]")))), ("Minimum number of unrolling of recursive functions to try (default 1)")))::(((FStar_Getopt.noshort), ("MLish"), (FStar_Getopt.ZeroArgs ((fun uu____1252 -> Bool (true)))), ("Trigger various specializations for compiling the F* compiler itself (not meant for user code)")))::(((FStar_Getopt.noshort), ("n_cores"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1262 = (FStar_Util.int_of_string x)
in Int (uu____1262)))), ("[positive integer]")))), ("Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")))::(((FStar_Getopt.noshort), ("no_default_includes"), (FStar_Getopt.ZeroArgs ((fun uu____1269 -> Bool (true)))), ("Ignore the default module search paths")))::(((FStar_Getopt.noshort), ("no_extract"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1279 = (

let uu____1281 = (

let uu____1283 = (get_no_extract ())
in (x)::uu____1283)
in (FStar_All.pipe_right uu____1281 (FStar_List.map (fun _0_35 -> String (_0_35)))))
in List (uu____1279)))), ("[module name]")))), ("Do not extract code from this module")))::(((FStar_Getopt.noshort), ("no_location_info"), (FStar_Getopt.ZeroArgs ((fun uu____1293 -> Bool (true)))), ("Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")))::(((FStar_Getopt.noshort), ("odir"), (FStar_Getopt.OneArg ((((fun _0_36 -> String (_0_36))), ("[dir]")))), ("Place output in directory [dir]")))::(((FStar_Getopt.noshort), ("prims"), (FStar_Getopt.OneArg ((((fun _0_37 -> String (_0_37))), ("file")))), ("")))::(((FStar_Getopt.noshort), ("print_before_norm"), (FStar_Getopt.ZeroArgs ((fun uu____1316 -> Bool (true)))), ("Do not normalize types before printing (for debugging)")))::(((FStar_Getopt.noshort), ("print_bound_var_types"), (FStar_Getopt.ZeroArgs ((fun uu____1323 -> Bool (true)))), ("Print the types of bound variables")))::(((FStar_Getopt.noshort), ("print_effect_args"), (FStar_Getopt.ZeroArgs ((fun uu____1330 -> Bool (true)))), ("Print inferred predicate transformers for all computation types")))::(((FStar_Getopt.noshort), ("print_fuels"), (FStar_Getopt.ZeroArgs ((fun uu____1337 -> Bool (true)))), ("Print the fuel amounts used for each successful query")))::(((FStar_Getopt.noshort), ("print_implicits"), (FStar_Getopt.ZeroArgs ((fun uu____1344 -> Bool (true)))), ("Print implicit arguments")))::(((FStar_Getopt.noshort), ("print_universes"), (FStar_Getopt.ZeroArgs ((fun uu____1351 -> Bool (true)))), ("Print universes")))::(((FStar_Getopt.noshort), ("print_z3_statistics"), (FStar_Getopt.ZeroArgs ((fun uu____1358 -> Bool (true)))), ("Print Z3 statistics for each SMT query")))::(((FStar_Getopt.noshort), ("prn"), (FStar_Getopt.ZeroArgs ((fun uu____1365 -> Bool (true)))), ("Print real names (you may want to use this in conjunction with log_queries)")))::(((FStar_Getopt.noshort), ("record_hints"), (FStar_Getopt.ZeroArgs ((fun uu____1372 -> Bool (true)))), ("Record a database of hints for efficient proof replay")))::(((FStar_Getopt.noshort), ("reuse_hint_for"), (FStar_Getopt.OneArg ((((fun _0_38 -> String (_0_38))), ("top-level name in the current module")))), ("Optimistically, attempt using the recorded hint for \'f\' when trying to verify some other term \'g\'")))::(((FStar_Getopt.noshort), ("show_signatures"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1390 = (

let uu____1392 = (

let uu____1394 = (get_show_signatures ())
in (x)::uu____1394)
in (FStar_All.pipe_right uu____1392 (FStar_List.map (fun _0_39 -> String (_0_39)))))
in List (uu____1390)))), ("[module name]")))), ("Show the checked signatures for all top-level symbols in the module")))::(((FStar_Getopt.noshort), ("silent"), (FStar_Getopt.ZeroArgs ((fun uu____1404 -> Bool (true)))), (" ")))::(((FStar_Getopt.noshort), ("smt"), (FStar_Getopt.OneArg ((((fun _0_40 -> String (_0_40))), ("[path]")))), ("Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)")))::(((FStar_Getopt.noshort), ("split_cases"), (FStar_Getopt.OneArg ((((fun n -> (

let uu____1422 = (FStar_Util.int_of_string n)
in Int (uu____1422)))), ("[positive integer]")))), ("Partition VC of a match into groups of [n] cases")))::(((FStar_Getopt.noshort), ("timing"), (FStar_Getopt.ZeroArgs ((fun uu____1429 -> Bool (true)))), ("Print the time it takes to verify each top-level definition")))::(((FStar_Getopt.noshort), ("trace_error"), (FStar_Getopt.ZeroArgs ((fun uu____1436 -> Bool (true)))), ("Don\'t print an error message; show an exception trace instead")))::(((FStar_Getopt.noshort), ("unthrottle_inductives"), (FStar_Getopt.ZeroArgs ((fun uu____1443 -> Bool (true)))), ("Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")))::(((FStar_Getopt.noshort), ("use_eq_at_higher_order"), (FStar_Getopt.ZeroArgs ((fun uu____1450 -> Bool (true)))), ("Use equality constraints when comparing higher-order types (Temporary)")))::(((FStar_Getopt.noshort), ("use_hints"), (FStar_Getopt.ZeroArgs ((fun uu____1457 -> Bool (true)))), ("Use a previously recorded hints database for proof replay")))::(((FStar_Getopt.noshort), ("verify_all"), (FStar_Getopt.ZeroArgs ((fun uu____1464 -> Bool (true)))), ("With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.")))::(((FStar_Getopt.noshort), ("verify_module"), (FStar_Getopt.OneArg (((cons_verify_module), ("[module name]")))), ("Name of the module to verify")))::(((FStar_Getopt.noshort), ("__temp_no_proj"), (FStar_Getopt.OneArg ((((fun x -> (

let uu____1482 = (

let uu____1484 = (

let uu____1486 = (get___temp_no_proj ())
in (x)::uu____1486)
in (FStar_All.pipe_right uu____1484 (FStar_List.map (fun _0_41 -> String (_0_41)))))
in List (uu____1482)))), ("[module name]")))), ("Don\'t generate projectors for this module")))::((('v'), ("version"), (FStar_Getopt.ZeroArgs ((fun uu____1496 -> ((display_version ());
(FStar_All.exit (Prims.parse_int "0"));
)))), ("Display version number")))::(((FStar_Getopt.noshort), ("warn_default_effects"), (FStar_Getopt.ZeroArgs ((fun uu____1504 -> Bool (true)))), ("Warn when (a -> b) is desugared to (a -> Tot b)")))::(((FStar_Getopt.noshort), ("z3cliopt"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1514 = (

let uu____1516 = (

let uu____1518 = (get_z3cliopt ())
in (FStar_List.append uu____1518 ((s)::[])))
in (FStar_All.pipe_right uu____1516 (FStar_List.map (fun _0_42 -> String (_0_42)))))
in List (uu____1514)))), ("[option]")))), ("Z3 command line options")))::(((FStar_Getopt.noshort), ("z3refresh"), (FStar_Getopt.ZeroArgs ((fun uu____1528 -> Bool (false)))), ("Restart Z3 after each query; useful for ensuring proof robustness")))::(((FStar_Getopt.noshort), ("z3rlimit"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1538 = (FStar_Util.int_of_string s)
in Int (uu____1538)))), ("[positive integer]")))), ("Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")))::(((FStar_Getopt.noshort), ("z3seed"), (FStar_Getopt.OneArg ((((fun s -> (

let uu____1548 = (FStar_Util.int_of_string s)
in Int (uu____1548)))), ("[positive integer]")))), ("Set the Z3 random seed (default 0)")))::(((FStar_Getopt.noshort), ("z3timeout"), (FStar_Getopt.OneArg ((((fun s -> ((FStar_Util.print_string "Warning: z3timeout ignored; use z3rlimit instead\n");
(

let uu____1559 = (FStar_Util.int_of_string s)
in Int (uu____1559));
))), ("[positive integer]")))), ("Set the Z3 per-query (soft) timeout to [t] seconds (default 5)")))::(((FStar_Getopt.noshort), ("__no_positivity"), (FStar_Getopt.ZeroArgs ((fun uu____1566 -> Bool (true)))), ("Don\'t check positivity of inductive types")))::[]
in (

let uu____1572 = (FStar_List.map mk_spec specs)
in ((('h'), ("help"), (FStar_Getopt.ZeroArgs ((fun x -> ((display_usage_aux specs);
(FStar_All.exit (Prims.parse_int "0"));
)))), ("Display this information")))::uu____1572)))
and parse_codegen : Prims.string  ->  Prims.string = (fun s -> (match (s) with
| ("Kremlin") | ("OCaml") | ("FSharp") -> begin
s
end
| uu____1593 -> begin
((FStar_Util.print_string "Wrong argument to codegen flag\n");
(

let uu____1596 = (specs ())
in (display_usage_aux uu____1596));
(FStar_All.exit (Prims.parse_int "1"));
)
end))
and validate_cardinality : Prims.string  ->  Prims.string = (fun x -> (match (x) with
| ("warn") | ("check") | ("off") -> begin
x
end
| uu____1604 -> begin
((FStar_Util.print_string "Wrong argument to cardinality flag\n");
(

let uu____1607 = (specs ())
in (display_usage_aux uu____1607));
(FStar_All.exit (Prims.parse_int "1"));
)
end))


let settable : Prims.string  ->  Prims.bool = (fun uu___49_1616 -> (match (uu___49_1616) with
| ("admit_smt_queries") | ("cardinality") | ("debug") | ("debug_level") | ("detail_errors") | ("eager_inference") | ("hide_genident_nums") | ("hide_uvar_nums") | ("hint_info") | ("initial_fuel") | ("initial_ifuel") | ("inline_arith") | ("lax") | ("log_types") | ("log_queries") | ("max_fuel") | ("max_ifuel") | ("min_fuel") | ("print_before_norm") | ("print_bound_var_types") | ("print_effect_args") | ("print_fuels") | ("print_implicits") | ("print_universes") | ("print_z3_statistics") | ("prn") | ("show_signatures") | ("silent") | ("split_cases") | ("timing") | ("trace_error") | ("unthrottle_inductives") | ("use_eq_at_higher_order") | ("__temp_no_proj") | ("no_warn_top_level_effects") | ("reuse_hint_for") | ("z3refresh") -> begin
true
end
| uu____1617 -> begin
false
end))


let resettable : Prims.string  ->  Prims.bool = (fun s -> ((((settable s) || (s = "z3timeout")) || (s = "z3rlimit")) || (s = "z3seed")))


let all_specs : FStar_Getopt.opt Prims.list = (specs ())


let settable_specs : (FStar_BaseTypes.char * Prims.string * Prims.unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____1640 -> (match (uu____1640) with
| (uu____1646, x, uu____1648, uu____1649) -> begin
(settable x)
end))))


let resettable_specs : (FStar_BaseTypes.char * Prims.string * Prims.unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____1670 -> (match (uu____1670) with
| (uu____1676, x, uu____1678, uu____1679) -> begin
(resettable x)
end))))


let display_usage : Prims.unit  ->  Prims.unit = (fun uu____1684 -> (

let uu____1685 = (specs ())
in (display_usage_aux uu____1685)))


let fstar_home : Prims.unit  ->  Prims.string = (fun uu____1694 -> (

let uu____1695 = (get_fstar_home ())
in (match (uu____1695) with
| None -> begin
(

let x = (FStar_Util.get_exec_dir ())
in (

let x = (Prims.strcat x "/..")
in ((set_option' (("fstar_home"), (String (x))));
x;
)))
end
| Some (x) -> begin
x
end)))


let set_options : options  ->  Prims.string  ->  FStar_Getopt.parse_cmdline_res = (fun o s -> (

let specs = (match (o) with
| Set -> begin
resettable_specs
end
| Reset -> begin
resettable_specs
end
| Restore -> begin
all_specs
end)
in (FStar_Getopt.parse_string specs (fun uu____1720 -> ()) s)))


let file_list_ : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let parse_cmd_line : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____1731 -> (

let res = (

let uu____1733 = (specs ())
in (FStar_Getopt.parse_cmdline uu____1733 (fun i -> (

let uu____1736 = (

let uu____1738 = (FStar_ST.read file_list_)
in (FStar_List.append uu____1738 ((i)::[])))
in (FStar_ST.write file_list_ uu____1736)))))
in (

let uu____1746 = (FStar_ST.read file_list_)
in ((res), (uu____1746)))))


let file_list : Prims.unit  ->  Prims.string Prims.list = (fun uu____1755 -> (FStar_ST.read file_list_))


let restore_cmd_line_options : Prims.bool  ->  FStar_Getopt.parse_cmdline_res = (fun should_clear -> (

let old_verify_module = (get_verify_module ())
in ((match (should_clear) with
| true -> begin
(clear ())
end
| uu____1765 -> begin
(init ())
end);
(

let r = (

let uu____1767 = (specs ())
in (FStar_Getopt.parse_cmdline uu____1767 (fun x -> ())))
in ((

let uu____1771 = (

let uu____1774 = (

let uu____1775 = (FStar_List.map (fun _0_43 -> String (_0_43)) old_verify_module)
in List (uu____1775))
in (("verify_module"), (uu____1774)))
in (set_option' uu____1771));
r;
));
)))


let should_verify : Prims.string  ->  Prims.bool = (fun m -> (

let uu____1780 = (get_lax ())
in (match (uu____1780) with
| true -> begin
false
end
| uu____1781 -> begin
(

let uu____1782 = (get_verify_all ())
in (match (uu____1782) with
| true -> begin
true
end
| uu____1783 -> begin
(

let uu____1784 = (get_verify_module ())
in (match (uu____1784) with
| [] -> begin
(

let uu____1786 = (file_list ())
in (FStar_List.existsML (fun f -> (

let f = (FStar_Util.basename f)
in (

let f = (

let uu____1791 = (

let uu____1792 = (

let uu____1793 = (

let uu____1794 = (FStar_Util.get_file_extension f)
in (FStar_String.length uu____1794))
in ((FStar_String.length f) - uu____1793))
in (uu____1792 - (Prims.parse_int "1")))
in (FStar_String.substring f (Prims.parse_int "0") uu____1791))
in ((FStar_String.lowercase f) = m)))) uu____1786))
end
| l -> begin
(FStar_List.contains (FStar_String.lowercase m) l)
end))
end))
end)))


let dont_gen_projectors : Prims.string  ->  Prims.bool = (fun m -> (

let uu____1804 = (get___temp_no_proj ())
in (FStar_List.contains m uu____1804)))


let should_print_message : Prims.string  ->  Prims.bool = (fun m -> (

let uu____1809 = (should_verify m)
in (match (uu____1809) with
| true -> begin
(m <> "Prims")
end
| uu____1810 -> begin
false
end)))


let include_path : Prims.unit  ->  Prims.string Prims.list = (fun uu____1814 -> (

let uu____1815 = (get_no_default_includes ())
in (match (uu____1815) with
| true -> begin
(get_include ())
end
| uu____1817 -> begin
(

let h = (fstar_home ())
in (

let defs = universe_include_path_base_dirs
in (

let uu____1821 = (

let uu____1823 = (FStar_All.pipe_right defs (FStar_List.map (fun x -> (Prims.strcat h x))))
in (FStar_All.pipe_right uu____1823 (FStar_List.filter FStar_Util.file_exists)))
in (

let uu____1830 = (

let uu____1832 = (get_include ())
in (FStar_List.append uu____1832 ((".")::[])))
in (FStar_List.append uu____1821 uu____1830)))))
end)))


let find_file : Prims.string  ->  Prims.string Prims.option = (fun filename -> (

let uu____1838 = (FStar_Util.is_path_absolute filename)
in (match (uu____1838) with
| true -> begin
(match ((FStar_Util.file_exists filename)) with
| true -> begin
Some (filename)
end
| uu____1841 -> begin
None
end)
end
| uu____1842 -> begin
(

let uu____1843 = (

let uu____1845 = (include_path ())
in (FStar_List.rev uu____1845))
in (FStar_Util.find_map uu____1843 (fun p -> (

let path = (FStar_Util.join_paths p filename)
in (match ((FStar_Util.file_exists path)) with
| true -> begin
Some (path)
end
| uu____1850 -> begin
None
end)))))
end)))


let prims : Prims.unit  ->  Prims.string = (fun uu____1853 -> (

let uu____1854 = (get_prims ())
in (match (uu____1854) with
| None -> begin
(

let filename = "prims.fst"
in (

let uu____1857 = (find_file filename)
in (match (uu____1857) with
| Some (result) -> begin
result
end
| None -> begin
(

let uu____1860 = (

let uu____1861 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in FStar_Util.Failure (uu____1861))
in (Prims.raise uu____1860))
end)))
end
| Some (x) -> begin
x
end)))


let prepend_output_dir : Prims.string  ->  Prims.string = (fun fname -> (

let uu____1866 = (get_odir ())
in (match (uu____1866) with
| None -> begin
fname
end
| Some (x) -> begin
(Prims.strcat x (Prims.strcat "/" fname))
end)))


let __temp_no_proj : Prims.string  ->  Prims.bool = (fun s -> (

let uu____1872 = (get___temp_no_proj ())
in (FStar_All.pipe_right uu____1872 (FStar_List.contains s))))


let admit_smt_queries : Prims.unit  ->  Prims.bool = (fun uu____1877 -> (get_admit_smt_queries ()))


let check_cardinality : Prims.unit  ->  Prims.bool = (fun uu____1880 -> (

let uu____1881 = (get_cardinality ())
in (uu____1881 = "check")))


let codegen : Prims.unit  ->  Prims.string Prims.option = (fun uu____1885 -> (get_codegen ()))


let codegen_libs : Prims.unit  ->  Prims.string Prims.list Prims.list = (fun uu____1890 -> (

let uu____1891 = (get_codegen_lib ())
in (FStar_All.pipe_right uu____1891 (FStar_List.map (fun x -> (FStar_Util.split x "."))))))


let debug_any : Prims.unit  ->  Prims.bool = (fun uu____1900 -> (

let uu____1901 = (get_debug ())
in (uu____1901 <> [])))


let debug_at_level : Prims.string  ->  debug_level_t  ->  Prims.bool = (fun modul level -> (((modul = "") || (

let uu____1910 = (get_debug ())
in (FStar_All.pipe_right uu____1910 (FStar_List.contains modul)))) && (debug_level_geq level)))


let dep : Prims.unit  ->  Prims.string Prims.option = (fun uu____1916 -> (get_dep ()))


let detail_errors : Prims.unit  ->  Prims.bool = (fun uu____1919 -> (get_detail_errors ()))


let doc : Prims.unit  ->  Prims.bool = (fun uu____1922 -> (get_doc ()))


let dump_module : Prims.string  ->  Prims.bool = (fun s -> (

let uu____1926 = (get_dump_module ())
in (FStar_All.pipe_right uu____1926 (FStar_List.contains s))))


let eager_inference : Prims.unit  ->  Prims.bool = (fun uu____1931 -> (get_eager_inference ()))


let explicit_deps : Prims.unit  ->  Prims.bool = (fun uu____1934 -> (get_explicit_deps ()))


let extract_all : Prims.unit  ->  Prims.bool = (fun uu____1937 -> (get_extract_all ()))


let fs_typ_app : Prims.string  ->  Prims.bool = (fun filename -> (

let uu____1941 = (FStar_ST.read light_off_files)
in (FStar_List.contains filename uu____1941)))


let full_context_dependency : Prims.unit  ->  Prims.bool = (fun uu____1948 -> true)


let hide_genident_nums : Prims.unit  ->  Prims.bool = (fun uu____1951 -> (get_hide_genident_nums ()))


let hide_uvar_nums : Prims.unit  ->  Prims.bool = (fun uu____1954 -> (get_hide_uvar_nums ()))


let hint_info : Prims.unit  ->  Prims.bool = (fun uu____1957 -> (get_hint_info ()))


let indent : Prims.unit  ->  Prims.bool = (fun uu____1960 -> (get_indent ()))


let initial_fuel : Prims.unit  ->  Prims.int = (fun uu____1963 -> (get_initial_fuel ()))


let initial_ifuel : Prims.unit  ->  Prims.int = (fun uu____1966 -> (get_initial_ifuel ()))


let inline_arith : Prims.unit  ->  Prims.bool = (fun uu____1969 -> (get_inline_arith ()))


let interactive : Prims.unit  ->  Prims.bool = (fun uu____1972 -> (get_in ()))


let lax : Prims.unit  ->  Prims.bool = (fun uu____1975 -> (get_lax ()))


let log_queries : Prims.unit  ->  Prims.bool = (fun uu____1978 -> (get_log_queries ()))


let log_types : Prims.unit  ->  Prims.bool = (fun uu____1981 -> (get_log_types ()))


let max_fuel : Prims.unit  ->  Prims.int = (fun uu____1984 -> (get_max_fuel ()))


let max_ifuel : Prims.unit  ->  Prims.int = (fun uu____1987 -> (get_max_ifuel ()))


let min_fuel : Prims.unit  ->  Prims.int = (fun uu____1990 -> (get_min_fuel ()))


let ml_ish : Prims.unit  ->  Prims.bool = (fun uu____1993 -> (get_MLish ()))


let set_ml_ish : Prims.unit  ->  Prims.unit = (fun uu____1996 -> (set_option "MLish" (Bool (true))))


let n_cores : Prims.unit  ->  Prims.int = (fun uu____1999 -> (get_n_cores ()))


let no_default_includes : Prims.unit  ->  Prims.bool = (fun uu____2002 -> (get_no_default_includes ()))


let no_extract : Prims.string  ->  Prims.bool = (fun s -> (

let uu____2006 = (get_no_extract ())
in (FStar_All.pipe_right uu____2006 (FStar_List.contains s))))


let no_location_info : Prims.unit  ->  Prims.bool = (fun uu____2011 -> (get_no_location_info ()))


let norm_then_print : Prims.unit  ->  Prims.bool = (fun uu____2014 -> (

let uu____2015 = (get_print_before_norm ())
in (uu____2015 = false)))


let output_dir : Prims.unit  ->  Prims.string Prims.option = (fun uu____2019 -> (get_odir ()))


let print_bound_var_types : Prims.unit  ->  Prims.bool = (fun uu____2022 -> (get_print_bound_var_types ()))


let print_effect_args : Prims.unit  ->  Prims.bool = (fun uu____2025 -> (get_print_effect_args ()))


let print_fuels : Prims.unit  ->  Prims.bool = (fun uu____2028 -> (get_print_fuels ()))


let print_implicits : Prims.unit  ->  Prims.bool = (fun uu____2031 -> (get_print_implicits ()))


let print_real_names : Prims.unit  ->  Prims.bool = (fun uu____2034 -> (get_prn ()))


let print_universes : Prims.unit  ->  Prims.bool = (fun uu____2037 -> (get_print_universes ()))


let print_z3_statistics : Prims.unit  ->  Prims.bool = (fun uu____2040 -> (get_print_z3_statistics ()))


let record_hints : Prims.unit  ->  Prims.bool = (fun uu____2043 -> (get_record_hints ()))


let reuse_hint_for : Prims.unit  ->  Prims.string Prims.option = (fun uu____2047 -> (get_reuse_hint_for ()))


let silent : Prims.unit  ->  Prims.bool = (fun uu____2050 -> (get_silent ()))


let split_cases : Prims.unit  ->  Prims.int = (fun uu____2053 -> (get_split_cases ()))


let timing : Prims.unit  ->  Prims.bool = (fun uu____2056 -> (get_timing ()))


let trace_error : Prims.unit  ->  Prims.bool = (fun uu____2059 -> (get_trace_error ()))


let unthrottle_inductives : Prims.unit  ->  Prims.bool = (fun uu____2062 -> (get_unthrottle_inductives ()))


let use_eq_at_higher_order : Prims.unit  ->  Prims.bool = (fun uu____2065 -> (get_use_eq_at_higher_order ()))


let use_hints : Prims.unit  ->  Prims.bool = (fun uu____2068 -> (get_use_hints ()))


let verify_all : Prims.unit  ->  Prims.bool = (fun uu____2071 -> (get_verify_all ()))


let verify_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____2075 -> (get_verify_module ()))


let warn_cardinality : Prims.unit  ->  Prims.bool = (fun uu____2078 -> (

let uu____2079 = (get_cardinality ())
in (uu____2079 = "warn")))


let warn_default_effects : Prims.unit  ->  Prims.bool = (fun uu____2082 -> (get_warn_default_effects ()))


let warn_top_level_effects : Prims.unit  ->  Prims.bool = (fun uu____2085 -> (get_warn_top_level_effects ()))


let z3_exe : Prims.unit  ->  Prims.string = (fun uu____2088 -> (

let uu____2089 = (get_smt ())
in (match (uu____2089) with
| None -> begin
(FStar_Platform.exe "z3")
end
| Some (s) -> begin
s
end)))


let z3_cliopt : Prims.unit  ->  Prims.string Prims.list = (fun uu____2095 -> (get_z3cliopt ()))


let z3_refresh : Prims.unit  ->  Prims.bool = (fun uu____2098 -> (get_z3refresh ()))


let z3_rlimit : Prims.unit  ->  Prims.int = (fun uu____2101 -> (get_z3rlimit ()))


let z3_seed : Prims.unit  ->  Prims.int = (fun uu____2104 -> (get_z3seed ()))


let z3_timeout : Prims.unit  ->  Prims.int = (fun uu____2107 -> (get_z3timeout ()))


let no_positivity : Prims.unit  ->  Prims.bool = (fun uu____2110 -> (get_no_positivity ()))


let should_extract : Prims.string  ->  Prims.bool = (fun m -> ((

let uu____2114 = (no_extract m)
in (not (uu____2114))) && ((extract_all ()) || (

let uu____2115 = (get_extract_module ())
in (match (uu____2115) with
| [] -> begin
(

let uu____2117 = (get_extract_namespace ())
in (match (uu____2117) with
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




