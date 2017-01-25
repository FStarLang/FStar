
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
Some ((as_t v))
end))


let fstar_options : option_val FStar_Util.smap Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let peek : Prims.unit  ->  option_val FStar_Util.smap = (fun uu____200 -> (FStar_List.hd (FStar_ST.read fstar_options)))


let pop : Prims.unit  ->  Prims.unit = (fun uu____208 -> (

let uu____209 = (FStar_ST.read fstar_options)
in (match (uu____209) with
| ([]) | ((_)::[]) -> begin
(failwith "TOO MANY POPS!")
end
| (uu____220)::tl -> begin
(FStar_ST.write fstar_options tl)
end)))


let push : Prims.unit  ->  Prims.unit = (fun uu____232 -> (let _0_18 = (let _0_17 = (FStar_Util.smap_copy (peek ()))
in (let _0_16 = (FStar_ST.read fstar_options)
in (_0_17)::_0_16))
in (FStar_ST.write fstar_options _0_18)))


let set_option : Prims.string  ->  option_val  ->  Prims.unit = (fun k v -> (let _0_19 = (peek ())
in (FStar_Util.smap_add _0_19 k v)))


let set_option' : (Prims.string * option_val)  ->  Prims.unit = (fun uu____252 -> (match (uu____252) with
| (k, v) -> begin
(set_option k v)
end))


let light_off_files : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let add_light_off_file : Prims.string  ->  Prims.unit = (fun filename -> (let _0_21 = (let _0_20 = (FStar_ST.read light_off_files)
in (filename)::_0_20)
in (FStar_ST.write light_off_files _0_21)))


let init : Prims.unit  ->  Prims.unit = (fun uu____273 -> (

let vals = ((("__temp_no_proj"), (List ([]))))::((("_fstar_home"), (String (""))))::((("_include_path"), (List ([]))))::((("admit_smt_queries"), (Bool (false))))::((("cardinality"), (String ("off"))))::((("codegen"), (Unset)))::((("codegen-lib"), (List ([]))))::((("debug"), (List ([]))))::((("debug_level"), (List ([]))))::((("dep"), (Unset)))::((("detail_errors"), (Bool (false))))::((("doc"), (Bool (false))))::((("dump_module"), (List ([]))))::((("eager_inference"), (Bool (false))))::((("explicit_deps"), (Bool (false))))::((("extract_all"), (Bool (false))))::((("extract_module"), (List ([]))))::((("extract_namespace"), (List ([]))))::((("fs_typ_app"), (Bool (false))))::((("fsi"), (Bool (false))))::((("fstar_home"), (Unset)))::((("full_context_dependency"), (Bool (true))))::((("hide_genident_nums"), (Bool (false))))::((("hide_uvar_nums"), (Bool (false))))::((("hint_info"), (Bool (false))))::((("in"), (Bool (false))))::((("include"), (List ([]))))::((("indent"), (Bool (false))))::((("initial_fuel"), (Int ((Prims.parse_int "2")))))::((("initial_ifuel"), (Int ((Prims.parse_int "1")))))::((("inline_arith"), (Bool (false))))::((("lax"), (Bool (false))))::((("log_queries"), (Bool (false))))::((("log_types"), (Bool (false))))::((("max_fuel"), (Int ((Prims.parse_int "8")))))::((("max_ifuel"), (Int ((Prims.parse_int "2")))))::((("min_fuel"), (Int ((Prims.parse_int "1")))))::((("MLish"), (Bool (false))))::((("n_cores"), (Int ((Prims.parse_int "1")))))::((("no_default_includes"), (Bool (false))))::((("no_extract"), (List ([]))))::((("no_location_info"), (Bool (false))))::((("odir"), (Unset)))::((("prims"), (Unset)))::((("pretype"), (Bool (true))))::((("prims_ref"), (Unset)))::((("print_before_norm"), (Bool (false))))::((("print_bound_var_types"), (Bool (false))))::((("print_effect_args"), (Bool (false))))::((("print_fuels"), (Bool (false))))::((("print_implicits"), (Bool (false))))::((("print_universes"), (Bool (false))))::((("print_z3_statistics"), (Bool (false))))::((("prn"), (Bool (false))))::((("record_hints"), (Bool (false))))::((("reuse_hint_for"), (Unset)))::((("show_signatures"), (List ([]))))::((("silent"), (Bool (false))))::((("smt"), (Unset)))::((("split_cases"), (Int ((Prims.parse_int "0")))))::((("timing"), (Bool (false))))::((("trace_error"), (Bool (false))))::((("unthrottle_inductives"), (Bool (false))))::((("use_eq_at_higher_order"), (Bool (false))))::((("use_hints"), (Bool (false))))::((("verify"), (Bool (true))))::((("verify_all"), (Bool (false))))::((("verify_module"), (List ([]))))::((("no_warn_top_level_effects"), (Bool (true))))::((("z3refresh"), (Bool (false))))::((("z3rlimit"), (Int ((Prims.parse_int "5")))))::((("z3seed"), (Int ((Prims.parse_int "0")))))::((("z3timeout"), (Int ((Prims.parse_int "5")))))::[]
in (

let o = (peek ())
in ((FStar_Util.smap_clear o);
(FStar_All.pipe_right vals (FStar_List.iter set_option'));
))))


let clear : Prims.unit  ->  Prims.unit = (fun uu____436 -> (

let o = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_ST.write fstar_options ((o)::[]));
(FStar_ST.write light_off_files []);
(init ());
)))


let _run : Prims.unit = (clear ())


let lookup_opt = (fun s c -> (

let uu____467 = (let _0_22 = (peek ())
in (FStar_Util.smap_try_find _0_22 s))
in (match (uu____467) with
| None -> begin
(failwith (Prims.strcat "Impossible: option " (Prims.strcat s " not found")))
end
| Some (s) -> begin
(c s)
end)))


let get_admit_smt_queries : Prims.unit  ->  Prims.bool = (fun uu____472 -> (lookup_opt "admit_smt_queries" as_bool))


let get_cardinality : Prims.unit  ->  Prims.string = (fun uu____475 -> (lookup_opt "cardinality" as_string))


let get_codegen : Prims.unit  ->  Prims.string Prims.option = (fun uu____479 -> (lookup_opt "codegen" (as_option as_string)))


let get_codegen_lib : Prims.unit  ->  Prims.string Prims.list = (fun uu____484 -> (lookup_opt "codegen-lib" (as_list as_string)))


let get_debug : Prims.unit  ->  Prims.string Prims.list = (fun uu____489 -> (lookup_opt "debug" (as_list as_string)))


let get_debug_level : Prims.unit  ->  Prims.string Prims.list = (fun uu____494 -> (lookup_opt "debug_level" (as_list as_string)))


let get_dep : Prims.unit  ->  Prims.string Prims.option = (fun uu____499 -> (lookup_opt "dep" (as_option as_string)))


let get_detail_errors : Prims.unit  ->  Prims.bool = (fun uu____503 -> (lookup_opt "detail_errors" as_bool))


let get_doc : Prims.unit  ->  Prims.bool = (fun uu____506 -> (lookup_opt "doc" as_bool))


let get_dump_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____510 -> (lookup_opt "dump_module" (as_list as_string)))


let get_eager_inference : Prims.unit  ->  Prims.bool = (fun uu____514 -> (lookup_opt "eager_inference" as_bool))


let get_explicit_deps : Prims.unit  ->  Prims.bool = (fun uu____517 -> (lookup_opt "explicit_deps" as_bool))


let get_extract_all : Prims.unit  ->  Prims.bool = (fun uu____520 -> (lookup_opt "extract_all" as_bool))


let get_extract_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____524 -> (lookup_opt "extract_module" (as_list as_string)))


let get_extract_namespace : Prims.unit  ->  Prims.string Prims.list = (fun uu____529 -> (lookup_opt "extract_namespace" (as_list as_string)))


let get_fs_typ_app : Prims.unit  ->  Prims.bool = (fun uu____533 -> (lookup_opt "fs_typ_app" as_bool))


let get_fstar_home : Prims.unit  ->  Prims.string Prims.option = (fun uu____537 -> (lookup_opt "fstar_home" (as_option as_string)))


let get_hide_genident_nums : Prims.unit  ->  Prims.bool = (fun uu____541 -> (lookup_opt "hide_genident_nums" as_bool))


let get_hide_uvar_nums : Prims.unit  ->  Prims.bool = (fun uu____544 -> (lookup_opt "hide_uvar_nums" as_bool))


let get_hint_info : Prims.unit  ->  Prims.bool = (fun uu____547 -> (lookup_opt "hint_info" as_bool))


let get_in : Prims.unit  ->  Prims.bool = (fun uu____550 -> (lookup_opt "in" as_bool))


let get_include : Prims.unit  ->  Prims.string Prims.list = (fun uu____554 -> (lookup_opt "include" (as_list as_string)))


let get_indent : Prims.unit  ->  Prims.bool = (fun uu____558 -> (lookup_opt "indent" as_bool))


let get_initial_fuel : Prims.unit  ->  Prims.int = (fun uu____561 -> (lookup_opt "initial_fuel" as_int))


let get_initial_ifuel : Prims.unit  ->  Prims.int = (fun uu____564 -> (lookup_opt "initial_ifuel" as_int))


let get_inline_arith : Prims.unit  ->  Prims.bool = (fun uu____567 -> (lookup_opt "inline_arith" as_bool))


let get_lax : Prims.unit  ->  Prims.bool = (fun uu____570 -> (lookup_opt "lax" as_bool))


let get_log_queries : Prims.unit  ->  Prims.bool = (fun uu____573 -> (lookup_opt "log_queries" as_bool))


let get_log_types : Prims.unit  ->  Prims.bool = (fun uu____576 -> (lookup_opt "log_types" as_bool))


let get_max_fuel : Prims.unit  ->  Prims.int = (fun uu____579 -> (lookup_opt "max_fuel" as_int))


let get_max_ifuel : Prims.unit  ->  Prims.int = (fun uu____582 -> (lookup_opt "max_ifuel" as_int))


let get_min_fuel : Prims.unit  ->  Prims.int = (fun uu____585 -> (lookup_opt "min_fuel" as_int))


let get_MLish : Prims.unit  ->  Prims.bool = (fun uu____588 -> (lookup_opt "MLish" as_bool))


let get_n_cores : Prims.unit  ->  Prims.int = (fun uu____591 -> (lookup_opt "n_cores" as_int))


let get_no_default_includes : Prims.unit  ->  Prims.bool = (fun uu____594 -> (lookup_opt "no_default_includes" as_bool))


let get_no_extract : Prims.unit  ->  Prims.string Prims.list = (fun uu____598 -> (lookup_opt "no_extract" (as_list as_string)))


let get_no_location_info : Prims.unit  ->  Prims.bool = (fun uu____602 -> (lookup_opt "no_location_info" as_bool))


let get_odir : Prims.unit  ->  Prims.string Prims.option = (fun uu____606 -> (lookup_opt "odir" (as_option as_string)))


let get_prims : Prims.unit  ->  Prims.string Prims.option = (fun uu____611 -> (lookup_opt "prims" (as_option as_string)))


let get_print_before_norm : Prims.unit  ->  Prims.bool = (fun uu____615 -> (lookup_opt "print_before_norm" as_bool))


let get_print_bound_var_types : Prims.unit  ->  Prims.bool = (fun uu____618 -> (lookup_opt "print_bound_var_types" as_bool))


let get_print_effect_args : Prims.unit  ->  Prims.bool = (fun uu____621 -> (lookup_opt "print_effect_args" as_bool))


let get_print_fuels : Prims.unit  ->  Prims.bool = (fun uu____624 -> (lookup_opt "print_fuels" as_bool))


let get_print_implicits : Prims.unit  ->  Prims.bool = (fun uu____627 -> (lookup_opt "print_implicits" as_bool))


let get_print_universes : Prims.unit  ->  Prims.bool = (fun uu____630 -> (lookup_opt "print_universes" as_bool))


let get_print_z3_statistics : Prims.unit  ->  Prims.bool = (fun uu____633 -> (lookup_opt "print_z3_statistics" as_bool))


let get_prn : Prims.unit  ->  Prims.bool = (fun uu____636 -> (lookup_opt "prn" as_bool))


let get_record_hints : Prims.unit  ->  Prims.bool = (fun uu____639 -> (lookup_opt "record_hints" as_bool))


let get_reuse_hint_for : Prims.unit  ->  Prims.string Prims.option = (fun uu____643 -> (lookup_opt "reuse_hint_for" (as_option as_string)))


let get_show_signatures : Prims.unit  ->  Prims.string Prims.list = (fun uu____648 -> (lookup_opt "show_signatures" (as_list as_string)))


let get_silent : Prims.unit  ->  Prims.bool = (fun uu____652 -> (lookup_opt "silent" as_bool))


let get_smt : Prims.unit  ->  Prims.string Prims.option = (fun uu____656 -> (lookup_opt "smt" (as_option as_string)))


let get_split_cases : Prims.unit  ->  Prims.int = (fun uu____660 -> (lookup_opt "split_cases" as_int))


let get_timing : Prims.unit  ->  Prims.bool = (fun uu____663 -> (lookup_opt "timing" as_bool))


let get_trace_error : Prims.unit  ->  Prims.bool = (fun uu____666 -> (lookup_opt "trace_error" as_bool))


let get_unthrottle_inductives : Prims.unit  ->  Prims.bool = (fun uu____669 -> (lookup_opt "unthrottle_inductives" as_bool))


let get_use_eq_at_higher_order : Prims.unit  ->  Prims.bool = (fun uu____672 -> (lookup_opt "use_eq_at_higher_order" as_bool))


let get_use_hints : Prims.unit  ->  Prims.bool = (fun uu____675 -> (lookup_opt "use_hints" as_bool))


let get_verify_all : Prims.unit  ->  Prims.bool = (fun uu____678 -> (lookup_opt "verify_all" as_bool))


let get_verify_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____682 -> (lookup_opt "verify_module" (as_list as_string)))


let get___temp_no_proj : Prims.unit  ->  Prims.string Prims.list = (fun uu____687 -> (lookup_opt "__temp_no_proj" (as_list as_string)))


let get_version : Prims.unit  ->  Prims.bool = (fun uu____691 -> (lookup_opt "version" as_bool))


let get_warn_top_level_effects : Prims.unit  ->  Prims.bool = (fun uu____694 -> (lookup_opt "no_warn_top_level_effects" as_bool))


let get_z3refresh : Prims.unit  ->  Prims.bool = (fun uu____697 -> (lookup_opt "z3refresh" as_bool))


let get_z3rlimit : Prims.unit  ->  Prims.int = (fun uu____700 -> (lookup_opt "z3rlimit" as_int))


let get_z3seed : Prims.unit  ->  Prims.int = (fun uu____703 -> (lookup_opt "z3seed" as_int))


let get_z3timeout : Prims.unit  ->  Prims.int = (fun uu____706 -> (lookup_opt "z3timeout" as_int))


let dlevel : Prims.string  ->  debug_level_t = (fun uu___48_709 -> (match (uu___48_709) with
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


let debug_level_geq : debug_level_t  ->  Prims.bool = (fun l2 -> (let _0_23 = (get_debug_level ())
in (FStar_All.pipe_right _0_23 (FStar_Util.for_some (fun l1 -> (one_debug_level_geq (dlevel l1) l2))))))


let include_path_base_dirs : Prims.string Prims.list = ("/lib")::("/lib/fstar")::[]


let universe_include_path_base_dirs : Prims.string Prims.list = ("/ulib")::("/lib/fstar")::[]


let display_version : Prims.unit  ->  Prims.unit = (fun uu____727 -> (FStar_Util.print_string (FStar_Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" FStar_Version.version FStar_Version.platform FStar_Version.compiler FStar_Version.date FStar_Version.commit)))


let display_usage_aux = (fun specs -> ((FStar_Util.print_string "fstar.exe [options] file[s]\n");
(FStar_List.iter (fun uu____755 -> (match (uu____755) with
| (uu____761, flag, p, doc) -> begin
(match (p) with
| FStar_Getopt.ZeroArgs (ig) -> begin
(match ((doc = "")) with
| true -> begin
(FStar_Util.print_string (let _0_24 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format1 "  --%s\n" _0_24)))
end
| uu____770 -> begin
(FStar_Util.print_string (let _0_25 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format2 "  --%s  %s\n" _0_25 doc)))
end)
end
| FStar_Getopt.OneArg (uu____771, argname) -> begin
(match ((doc = "")) with
| true -> begin
(FStar_Util.print_string (let _0_27 = (FStar_Util.colorize_bold flag)
in (let _0_26 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format2 "  --%s %s\n" _0_27 _0_26))))
end
| uu____777 -> begin
(FStar_Util.print_string (let _0_29 = (FStar_Util.colorize_bold flag)
in (let _0_28 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format3 "  --%s %s  %s\n" _0_29 _0_28 doc))))
end)
end)
end)) specs);
))


let mk_spec : (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant * Prims.string)  ->  FStar_Getopt.opt = (fun o -> (

let uu____791 = o
in (match (uu____791) with
| (ns, name, arg, desc) -> begin
(

let arg = (match (arg) with
| FStar_Getopt.ZeroArgs (f) -> begin
(

let g = (fun uu____812 -> (set_option' (let _0_30 = (f ())
in ((name), (_0_30)))))
in FStar_Getopt.ZeroArgs (g))
end
| FStar_Getopt.OneArg (f, d) -> begin
(

let g = (fun x -> (set_option' (let _0_31 = (f x)
in ((name), (_0_31)))))
in FStar_Getopt.OneArg (((g), (d))))
end)
in ((ns), (name), (arg), (desc)))
end)))


let cons_extract_module : Prims.string  ->  option_val = (fun s -> List ((let _0_34 = (let _0_32 = (get_extract_module ())
in ((FStar_String.lowercase s))::_0_32)
in (FStar_All.pipe_right _0_34 (FStar_List.map (fun _0_33 -> String (_0_33)))))))


let cons_extract_namespace : Prims.string  ->  option_val = (fun s -> List ((let _0_37 = (let _0_35 = (get_extract_namespace ())
in ((FStar_String.lowercase s))::_0_35)
in (FStar_All.pipe_right _0_37 (FStar_List.map (fun _0_36 -> String (_0_36)))))))


let add_extract_module : Prims.string  ->  Prims.unit = (fun s -> (let _0_38 = (cons_extract_module s)
in (set_option "extract_module" _0_38)))


let add_extract_namespace : Prims.string  ->  Prims.unit = (fun s -> (let _0_39 = (cons_extract_namespace s)
in (set_option "extract_namespace" _0_39)))


let cons_verify_module : Prims.string  ->  option_val = (fun s -> List ((let _0_42 = (let _0_40 = (get_verify_module ())
in ((FStar_String.lowercase s))::_0_40)
in (FStar_All.pipe_right _0_42 (FStar_List.map (fun _0_41 -> String (_0_41)))))))


let add_verify_module : Prims.string  ->  Prims.unit = (fun s -> (let _0_43 = (cons_verify_module s)
in (set_option "verify_module" _0_43)))


let rec specs : Prims.unit  ->  FStar_Getopt.opt Prims.list = (fun uu____857 -> (

let specs = (((FStar_Getopt.noshort), ("admit_smt_queries"), (FStar_Getopt.OneArg ((((fun s -> (match ((s = "true")) with
| true -> begin
Bool (true)
end
| uu____875 -> begin
(match ((s = "false")) with
| true -> begin
Bool (false)
end
| uu____876 -> begin
(failwith "Invalid argument to --admit_smt_queries")
end)
end))), ("[true|false]")))), ("Admit SMT queries, unsafe! (default \'false\')")))::(((FStar_Getopt.noshort), ("cardinality"), (FStar_Getopt.OneArg ((((fun x -> String ((validate_cardinality x)))), ("[off|warn|check]")))), ("Check cardinality constraints on inductive data types (default \'off\')")))::(((FStar_Getopt.noshort), ("codegen"), (FStar_Getopt.OneArg ((((fun s -> String ((parse_codegen s)))), ("[OCaml|FSharp|Kremlin]")))), ("Generate code for execution")))::(((FStar_Getopt.noshort), ("codegen-lib"), (FStar_Getopt.OneArg ((((fun s -> List ((let _0_46 = (let _0_44 = (get_codegen_lib ())
in (s)::_0_44)
in (FStar_All.pipe_right _0_46 (FStar_List.map (fun _0_45 -> String (_0_45)))))))), ("[namespace]")))), ("External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")))::(((FStar_Getopt.noshort), ("debug"), (FStar_Getopt.OneArg ((((fun x -> List ((let _0_49 = (let _0_47 = (get_debug ())
in (x)::_0_47)
in (FStar_All.pipe_right _0_49 (FStar_List.map (fun _0_48 -> String (_0_48)))))))), ("[module name]")))), ("Print lots of debugging information while checking module")))::(((FStar_Getopt.noshort), ("debug_level"), (FStar_Getopt.OneArg ((((fun x -> List ((let _0_52 = (let _0_50 = (get_debug_level ())
in (x)::_0_50)
in (FStar_All.pipe_right _0_52 (FStar_List.map (fun _0_51 -> String (_0_51)))))))), ("[Low|Medium|High|Extreme|...]")))), ("Control the verbosity of debugging info")))::(((FStar_Getopt.noshort), ("dep"), (FStar_Getopt.OneArg ((((fun x -> (match (((x = "make") || (x = "graph"))) with
| true -> begin
String (x)
end
| uu____937 -> begin
(failwith "invalid argument to \'dep\'")
end))), ("[make|graph]")))), ("Output the transitive closure of the dependency graph in a format suitable for the given tool")))::(((FStar_Getopt.noshort), ("detail_errors"), (FStar_Getopt.ZeroArgs ((fun uu____944 -> Bool (true)))), ("Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")))::(((FStar_Getopt.noshort), ("doc"), (FStar_Getopt.ZeroArgs ((fun uu____951 -> Bool (true)))), ("Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")))::(((FStar_Getopt.noshort), ("dump_module"), (FStar_Getopt.OneArg ((((fun x -> (let _0_57 = (let _0_55 = (let _0_53 = (get_dump_module ())
in (x)::_0_53)
in (FStar_All.pipe_right _0_55 (FStar_List.map (fun _0_54 -> String (_0_54)))))
in (FStar_All.pipe_right _0_57 (fun _0_56 -> List (_0_56)))))), ("[module name]")))), ("")))::(((FStar_Getopt.noshort), ("eager_inference"), (FStar_Getopt.ZeroArgs ((fun uu____970 -> Bool (true)))), ("Solve all type-inference constraints eagerly; more efficient but at the cost of generality")))::(((FStar_Getopt.noshort), ("explicit_deps"), (FStar_Getopt.ZeroArgs ((fun uu____977 -> Bool (true)))), ("Do not find dependencies automatically, the user provides them on the command-line")))::(((FStar_Getopt.noshort), ("extract_all"), (FStar_Getopt.ZeroArgs ((fun uu____984 -> Bool (true)))), ("Discover the complete dependency graph and do not stop at interface boundaries")))::(((FStar_Getopt.noshort), ("extract_module"), (FStar_Getopt.OneArg (((cons_extract_module), ("[module name]")))), ("Only extract the specified modules (instead of the possibly-partial dependency graph)")))::(((FStar_Getopt.noshort), ("extract_namespace"), (FStar_Getopt.OneArg (((cons_extract_namespace), ("[namespace name]")))), ("Only extract modules in the specified namespace")))::(((FStar_Getopt.noshort), ("fs_typ_app"), (FStar_Getopt.ZeroArgs ((fun uu____1007 -> Bool (true)))), ("Allow the use of t<t1,...,tn> syntax for type applications;\n        brittle since it clashes with the integer less-than operator")))::(((FStar_Getopt.noshort), ("fstar_home"), (FStar_Getopt.OneArg ((((fun _0_58 -> String (_0_58))), ("[dir]")))), ("Set the FSTAR_HOME variable to [dir]")))::(((FStar_Getopt.noshort), ("hide_genident_nums"), (FStar_Getopt.ZeroArgs ((fun uu____1022 -> Bool (true)))), ("Don\'t print generated identifier numbers")))::(((FStar_Getopt.noshort), ("hide_uvar_nums"), (FStar_Getopt.ZeroArgs ((fun uu____1029 -> Bool (true)))), ("Don\'t print unification variable numbers")))::(((FStar_Getopt.noshort), ("hint_info"), (FStar_Getopt.ZeroArgs ((fun uu____1036 -> Bool (true)))), ("Print information regarding hints")))::(((FStar_Getopt.noshort), ("in"), (FStar_Getopt.ZeroArgs ((fun uu____1043 -> Bool (true)))), ("Interactive mode; reads input from stdin")))::(((FStar_Getopt.noshort), ("include"), (FStar_Getopt.OneArg ((((fun s -> List ((let _0_61 = (let _0_59 = (get_include ())
in (FStar_List.append _0_59 ((s)::[])))
in (FStar_All.pipe_right _0_61 (FStar_List.map (fun _0_60 -> String (_0_60)))))))), ("[path]")))), ("A directory in which to search for files included on the command line")))::(((FStar_Getopt.noshort), ("indent"), (FStar_Getopt.ZeroArgs ((fun uu____1061 -> Bool (true)))), ("Parses and outputs the files on the command line")))::(((FStar_Getopt.noshort), ("initial_fuel"), (FStar_Getopt.OneArg ((((fun x -> Int ((FStar_Util.int_of_string x)))), ("[non-negative integer]")))), ("Number of unrolling of recursive functions to try initially (default 2)")))::(((FStar_Getopt.noshort), ("initial_ifuel"), (FStar_Getopt.OneArg ((((fun x -> Int ((FStar_Util.int_of_string x)))), ("[non-negative integer]")))), ("Number of unrolling of inductive datatypes to try at first (default 1)")))::(((FStar_Getopt.noshort), ("inline_arith"), (FStar_Getopt.ZeroArgs ((fun uu____1086 -> Bool (true)))), ("Inline definitions of arithmetic functions in the SMT encoding")))::(((FStar_Getopt.noshort), ("lax"), (FStar_Getopt.ZeroArgs ((fun uu____1093 -> Bool (true)))), ("Run the lax-type checker only (admit all verification conditions)")))::(((FStar_Getopt.noshort), ("log_types"), (FStar_Getopt.ZeroArgs ((fun uu____1100 -> Bool (true)))), ("Print types computed for data/val/let-bindings")))::(((FStar_Getopt.noshort), ("log_queries"), (FStar_Getopt.ZeroArgs ((fun uu____1107 -> Bool (true)))), ("Log the Z3 queries in several queries-*.smt2 files, as we go")))::(((FStar_Getopt.noshort), ("max_fuel"), (FStar_Getopt.OneArg ((((fun x -> Int ((FStar_Util.int_of_string x)))), ("[non-negative integer]")))), ("Number of unrolling of recursive functions to try at most (default 8)")))::(((FStar_Getopt.noshort), ("max_ifuel"), (FStar_Getopt.OneArg ((((fun x -> Int ((FStar_Util.int_of_string x)))), ("[non-negative integer]")))), ("Number of unrolling of inductive datatypes to try at most (default 2)")))::(((FStar_Getopt.noshort), ("min_fuel"), (FStar_Getopt.OneArg ((((fun x -> Int ((FStar_Util.int_of_string x)))), ("[non-negative integer]")))), ("Minimum number of unrolling of recursive functions to try (default 1)")))::(((FStar_Getopt.noshort), ("MLish"), (FStar_Getopt.ZeroArgs ((fun uu____1141 -> Bool (true)))), ("Introduce unification variables that are only dependent on the type variables in the context")))::(((FStar_Getopt.noshort), ("n_cores"), (FStar_Getopt.OneArg ((((fun x -> Int ((FStar_Util.int_of_string x)))), ("[positive integer]")))), ("Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")))::(((FStar_Getopt.noshort), ("no_default_includes"), (FStar_Getopt.ZeroArgs ((fun uu____1157 -> Bool (true)))), ("Ignore the default module search paths")))::(((FStar_Getopt.noshort), ("no_extract"), (FStar_Getopt.OneArg ((((fun x -> List ((let _0_64 = (let _0_62 = (get_no_extract ())
in (x)::_0_62)
in (FStar_All.pipe_right _0_64 (FStar_List.map (fun _0_63 -> String (_0_63)))))))), ("[module name]")))), ("Do not extract code from this module")))::(((FStar_Getopt.noshort), ("no_location_info"), (FStar_Getopt.ZeroArgs ((fun uu____1175 -> Bool (true)))), ("Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")))::(((FStar_Getopt.noshort), ("odir"), (FStar_Getopt.OneArg ((((fun _0_65 -> String (_0_65))), ("[dir]")))), ("Place output in directory [dir]")))::(((FStar_Getopt.noshort), ("prims"), (FStar_Getopt.OneArg ((((fun _0_66 -> String (_0_66))), ("file")))), ("")))::(((FStar_Getopt.noshort), ("print_before_norm"), (FStar_Getopt.ZeroArgs ((fun uu____1198 -> Bool (true)))), ("Do not normalize types before printing (for debugging)")))::(((FStar_Getopt.noshort), ("print_bound_var_types"), (FStar_Getopt.ZeroArgs ((fun uu____1205 -> Bool (true)))), ("Print the types of bound variables")))::(((FStar_Getopt.noshort), ("print_effect_args"), (FStar_Getopt.ZeroArgs ((fun uu____1212 -> Bool (true)))), ("Print inferred predicate transformers for all computation types")))::(((FStar_Getopt.noshort), ("print_fuels"), (FStar_Getopt.ZeroArgs ((fun uu____1219 -> Bool (true)))), ("Print the fuel amounts used for each successful query")))::(((FStar_Getopt.noshort), ("print_implicits"), (FStar_Getopt.ZeroArgs ((fun uu____1226 -> Bool (true)))), ("Print implicit arguments")))::(((FStar_Getopt.noshort), ("print_universes"), (FStar_Getopt.ZeroArgs ((fun uu____1233 -> Bool (true)))), ("Print universes")))::(((FStar_Getopt.noshort), ("print_z3_statistics"), (FStar_Getopt.ZeroArgs ((fun uu____1240 -> Bool (true)))), ("Print Z3 statistics for each SMT query")))::(((FStar_Getopt.noshort), ("prn"), (FStar_Getopt.ZeroArgs ((fun uu____1247 -> Bool (true)))), ("Print real names (you may want to use this in conjunction with log_queries)")))::(((FStar_Getopt.noshort), ("record_hints"), (FStar_Getopt.ZeroArgs ((fun uu____1254 -> Bool (true)))), ("Record a database of hints for efficient proof replay")))::(((FStar_Getopt.noshort), ("reuse_hint_for"), (FStar_Getopt.OneArg ((((fun _0_67 -> String (_0_67))), ("top-level name in the current module")))), ("Optimistically, attempt using the recorded hint for \'f\' when trying to verify some other term \'g\'")))::(((FStar_Getopt.noshort), ("show_signatures"), (FStar_Getopt.OneArg ((((fun x -> List ((let _0_70 = (let _0_68 = (get_show_signatures ())
in (x)::_0_68)
in (FStar_All.pipe_right _0_70 (FStar_List.map (fun _0_69 -> String (_0_69)))))))), ("[module name]")))), ("Show the checked signatures for all top-level symbols in the module")))::(((FStar_Getopt.noshort), ("silent"), (FStar_Getopt.ZeroArgs ((fun uu____1280 -> Bool (true)))), (" ")))::(((FStar_Getopt.noshort), ("smt"), (FStar_Getopt.OneArg ((((fun _0_71 -> String (_0_71))), ("[path]")))), ("Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)")))::(((FStar_Getopt.noshort), ("split_cases"), (FStar_Getopt.OneArg ((((fun n -> Int ((FStar_Util.int_of_string n)))), ("[positive integer]")))), ("Partition VC of a match into groups of [n] cases")))::(((FStar_Getopt.noshort), ("timing"), (FStar_Getopt.ZeroArgs ((fun uu____1304 -> Bool (true)))), ("Print the time it takes to verify each top-level definition")))::(((FStar_Getopt.noshort), ("trace_error"), (FStar_Getopt.ZeroArgs ((fun uu____1311 -> Bool (true)))), ("Don\'t print an error message; show an exception trace instead")))::(((FStar_Getopt.noshort), ("unthrottle_inductives"), (FStar_Getopt.ZeroArgs ((fun uu____1318 -> Bool (true)))), ("Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")))::(((FStar_Getopt.noshort), ("use_eq_at_higher_order"), (FStar_Getopt.ZeroArgs ((fun uu____1325 -> Bool (true)))), ("Use equality constraints when comparing higher-order types (Temporary)")))::(((FStar_Getopt.noshort), ("use_hints"), (FStar_Getopt.ZeroArgs ((fun uu____1332 -> Bool (true)))), ("Use a previously recorded hints database for proof replay")))::(((FStar_Getopt.noshort), ("verify_all"), (FStar_Getopt.ZeroArgs ((fun uu____1339 -> Bool (true)))), ("With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.")))::(((FStar_Getopt.noshort), ("verify_module"), (FStar_Getopt.OneArg (((cons_verify_module), ("[module name]")))), ("Name of the module to verify")))::(((FStar_Getopt.noshort), ("__temp_no_proj"), (FStar_Getopt.OneArg ((((fun x -> List ((let _0_74 = (let _0_72 = (get___temp_no_proj ())
in (x)::_0_72)
in (FStar_All.pipe_right _0_74 (FStar_List.map (fun _0_73 -> String (_0_73)))))))), ("[module name]")))), ("Don\'t generate projectors for this module")))::((('v'), ("version"), (FStar_Getopt.ZeroArgs ((fun uu____1365 -> ((display_version ());
(FStar_All.exit (Prims.parse_int "0"));
)))), ("Display version number")))::(((FStar_Getopt.noshort), ("no_warn_top_level_effects"), (FStar_Getopt.ZeroArgs ((fun uu____1373 -> Bool (false)))), ("Top-level effects are checked by default; turn this flag on to prevent warning when this happens")))::(((FStar_Getopt.noshort), ("z3refresh"), (FStar_Getopt.ZeroArgs ((fun uu____1380 -> Bool (false)))), ("Restart Z3 after each query; useful for ensuring proof robustness")))::(((FStar_Getopt.noshort), ("z3rlimit"), (FStar_Getopt.OneArg ((((fun s -> Int ((FStar_Util.int_of_string s)))), ("[positive integer]")))), ("Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")))::(((FStar_Getopt.noshort), ("z3seed"), (FStar_Getopt.OneArg ((((fun s -> Int ((FStar_Util.int_of_string s)))), ("[positive integer]")))), ("Set the Z3 random seed (default 0)")))::(((FStar_Getopt.noshort), ("z3timeout"), (FStar_Getopt.OneArg ((((fun s -> ((FStar_Util.print_string "Warning: z3timeout ignored; use z3rlimit instead\n");
Int ((FStar_Util.int_of_string s));
))), ("[positive integer]")))), ("Set the Z3 per-query (soft) timeout to [t] seconds (default 5)")))::[]
in (let _0_75 = (FStar_List.map mk_spec specs)
in ((('h'), ("help"), (FStar_Getopt.ZeroArgs ((fun x -> ((display_usage_aux specs);
(FStar_All.exit (Prims.parse_int "0"));
)))), ("Display this information")))::_0_75)))
and parse_codegen : Prims.string  ->  Prims.string = (fun s -> (match (s) with
| ("Kremlin") | ("OCaml") | ("FSharp") -> begin
s
end
| uu____1428 -> begin
((FStar_Util.print_string "Wrong argument to codegen flag\n");
(display_usage_aux (specs ()));
(FStar_All.exit (Prims.parse_int "1"));
)
end))
and validate_cardinality : Prims.string  ->  Prims.string = (fun x -> (match (x) with
| ("warn") | ("check") | ("off") -> begin
x
end
| uu____1432 -> begin
((FStar_Util.print_string "Wrong argument to cardinality flag\n");
(display_usage_aux (specs ()));
(FStar_All.exit (Prims.parse_int "1"));
)
end))


let settable : Prims.string  ->  Prims.bool = (fun uu___49_1437 -> (match (uu___49_1437) with
| ("admit_smt_queries") | ("cardinality") | ("debug") | ("debug_level") | ("detail_errors") | ("eager_inference") | ("hide_genident_nums") | ("hide_uvar_nums") | ("hint_info") | ("initial_fuel") | ("initial_ifuel") | ("inline_arith") | ("lax") | ("log_types") | ("log_queries") | ("max_fuel") | ("max_ifuel") | ("min_fuel") | ("print_before_norm") | ("print_bound_var_types") | ("print_effect_args") | ("print_fuels") | ("print_implicits") | ("print_universes") | ("print_z3_statistics") | ("prn") | ("show_signatures") | ("silent") | ("split_cases") | ("timing") | ("trace_error") | ("unthrottle_inductives") | ("use_eq_at_higher_order") | ("__temp_no_proj") | ("no_warn_top_level_effects") | ("reuse_hint_for") | ("z3refresh") -> begin
true
end
| uu____1438 -> begin
false
end))


let resettable : Prims.string  ->  Prims.bool = (fun s -> ((((settable s) || (s = "z3timeout")) || (s = "z3rlimit")) || (s = "z3seed")))


let all_specs : FStar_Getopt.opt Prims.list = (specs ())


let settable_specs : (FStar_BaseTypes.char * Prims.string * Prims.unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____1461 -> (match (uu____1461) with
| (uu____1467, x, uu____1469, uu____1470) -> begin
(settable x)
end))))


let resettable_specs : (FStar_BaseTypes.char * Prims.string * Prims.unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun uu____1491 -> (match (uu____1491) with
| (uu____1497, x, uu____1499, uu____1500) -> begin
(resettable x)
end))))


let display_usage : Prims.unit  ->  Prims.unit = (fun uu____1505 -> (display_usage_aux (specs ())))


let fstar_home : Prims.unit  ->  Prims.string = (fun uu____1508 -> (

let uu____1509 = (get_fstar_home ())
in (match (uu____1509) with
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
in (FStar_Getopt.parse_string specs (fun uu____1534 -> ()) s)))


let file_list_ : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let parse_cmd_line : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun uu____1545 -> (

let res = (let _0_78 = (specs ())
in (FStar_Getopt.parse_cmdline _0_78 (fun i -> (let _0_77 = (let _0_76 = (FStar_ST.read file_list_)
in (FStar_List.append _0_76 ((i)::[])))
in (FStar_ST.write file_list_ _0_77)))))
in (let _0_79 = (FStar_ST.read file_list_)
in ((res), (_0_79)))))


let file_list : Prims.unit  ->  Prims.string Prims.list = (fun uu____1561 -> (FStar_ST.read file_list_))


let restore_cmd_line_options : Prims.bool  ->  FStar_Getopt.parse_cmdline_res = (fun should_clear -> (

let old_verify_module = (get_verify_module ())
in ((match (should_clear) with
| true -> begin
(clear ())
end
| uu____1571 -> begin
(init ())
end);
(

let r = (let _0_80 = (specs ())
in (FStar_Getopt.parse_cmdline _0_80 (fun x -> ())))
in ((set_option' (let _0_82 = List ((FStar_List.map (fun _0_81 -> String (_0_81)) old_verify_module))
in (("verify_module"), (_0_82))));
r;
));
)))


let should_verify : Prims.string  ->  Prims.bool = (fun m -> (

let uu____1578 = (get_lax ())
in (match (uu____1578) with
| true -> begin
false
end
| uu____1579 -> begin
(

let uu____1580 = (get_verify_all ())
in (match (uu____1580) with
| true -> begin
true
end
| uu____1581 -> begin
(

let uu____1582 = (get_verify_module ())
in (match (uu____1582) with
| [] -> begin
(let _0_86 = (file_list ())
in (FStar_List.existsML (fun f -> (

let f = (FStar_Util.basename f)
in (

let f = (let _0_85 = (let _0_84 = (let _0_83 = (FStar_String.length (FStar_Util.get_file_extension f))
in ((FStar_String.length f) - _0_83))
in (_0_84 - (Prims.parse_int "1")))
in (FStar_String.substring f (Prims.parse_int "0") _0_85))
in ((FStar_String.lowercase f) = m)))) _0_86))
end
| l -> begin
(FStar_List.contains (FStar_String.lowercase m) l)
end))
end))
end)))


let dont_gen_projectors : Prims.string  ->  Prims.bool = (fun m -> (let _0_87 = (get___temp_no_proj ())
in (FStar_List.contains m _0_87)))


let should_print_message : Prims.string  ->  Prims.bool = (fun m -> (

let uu____1600 = (should_verify m)
in (match (uu____1600) with
| true -> begin
(m <> "Prims")
end
| uu____1601 -> begin
false
end)))


let include_path : Prims.unit  ->  Prims.string Prims.list = (fun uu____1605 -> (

let uu____1606 = (get_no_default_includes ())
in (match (uu____1606) with
| true -> begin
(get_include ())
end
| uu____1608 -> begin
(

let h = (fstar_home ())
in (

let defs = universe_include_path_base_dirs
in (let _0_91 = (let _0_88 = (FStar_All.pipe_right defs (FStar_List.map (fun x -> (Prims.strcat h x))))
in (FStar_All.pipe_right _0_88 (FStar_List.filter FStar_Util.file_exists)))
in (let _0_90 = (let _0_89 = (get_include ())
in (FStar_List.append _0_89 ((".")::[])))
in (FStar_List.append _0_91 _0_90)))))
end)))


let find_file : Prims.string  ->  Prims.string Prims.option = (fun filename -> (

let uu____1621 = (FStar_Util.is_path_absolute filename)
in (match (uu____1621) with
| true -> begin
(match ((FStar_Util.file_exists filename)) with
| true -> begin
Some (filename)
end
| uu____1624 -> begin
None
end)
end
| uu____1625 -> begin
(let _0_92 = (FStar_List.rev (include_path ()))
in (FStar_Util.find_map _0_92 (fun p -> (

let path = (FStar_Util.join_paths p filename)
in (match ((FStar_Util.file_exists path)) with
| true -> begin
Some (path)
end
| uu____1629 -> begin
None
end)))))
end)))


let prims : Prims.unit  ->  Prims.string = (fun uu____1632 -> (

let uu____1633 = (get_prims ())
in (match (uu____1633) with
| None -> begin
(

let filename = "prims.fst"
in (

let uu____1636 = (find_file filename)
in (match (uu____1636) with
| Some (result) -> begin
result
end
| None -> begin
(Prims.raise (FStar_Util.Failure ((FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename))))
end)))
end
| Some (x) -> begin
x
end)))


let prepend_output_dir : Prims.string  ->  Prims.string = (fun fname -> (

let uu____1643 = (get_odir ())
in (match (uu____1643) with
| None -> begin
fname
end
| Some (x) -> begin
(Prims.strcat x (Prims.strcat "/" fname))
end)))


let __temp_no_proj : Prims.string  ->  Prims.bool = (fun s -> (let _0_93 = (get___temp_no_proj ())
in (FStar_All.pipe_right _0_93 (FStar_List.contains s))))


let admit_smt_queries : Prims.unit  ->  Prims.bool = (fun uu____1652 -> (get_admit_smt_queries ()))


let check_cardinality : Prims.unit  ->  Prims.bool = (fun uu____1655 -> (let _0_94 = (get_cardinality ())
in (_0_94 = "check")))


let codegen : Prims.unit  ->  Prims.string Prims.option = (fun uu____1659 -> (get_codegen ()))


let codegen_libs : Prims.unit  ->  Prims.string Prims.list Prims.list = (fun uu____1664 -> (let _0_95 = (get_codegen_lib ())
in (FStar_All.pipe_right _0_95 (FStar_List.map (fun x -> (FStar_Util.split x "."))))))


let debug_any : Prims.unit  ->  Prims.bool = (fun uu____1672 -> (let _0_96 = (get_debug ())
in (_0_96 <> [])))


let debug_at_level : Prims.string  ->  debug_level_t  ->  Prims.bool = (fun modul level -> (((modul = "") || (let _0_97 = (get_debug ())
in (FStar_All.pipe_right _0_97 (FStar_List.contains modul)))) && (debug_level_geq level)))


let dep : Prims.unit  ->  Prims.string Prims.option = (fun uu____1684 -> (get_dep ()))


let detail_errors : Prims.unit  ->  Prims.bool = (fun uu____1687 -> (get_detail_errors ()))


let doc : Prims.unit  ->  Prims.bool = (fun uu____1690 -> (get_doc ()))


let dump_module : Prims.string  ->  Prims.bool = (fun s -> (let _0_98 = (get_dump_module ())
in (FStar_All.pipe_right _0_98 (FStar_List.contains s))))


let eager_inference : Prims.unit  ->  Prims.bool = (fun uu____1697 -> (get_eager_inference ()))


let explicit_deps : Prims.unit  ->  Prims.bool = (fun uu____1700 -> (get_explicit_deps ()))


let extract_all : Prims.unit  ->  Prims.bool = (fun uu____1703 -> (get_extract_all ()))


let fs_typ_app : Prims.string  ->  Prims.bool = (fun filename -> ((get_fs_typ_app ()) && (let _0_99 = (FStar_ST.read light_off_files)
in (FStar_List.contains filename _0_99))))


let full_context_dependency : Prims.unit  ->  Prims.bool = (fun uu____1712 -> true)


let hide_genident_nums : Prims.unit  ->  Prims.bool = (fun uu____1715 -> (get_hide_genident_nums ()))


let hide_uvar_nums : Prims.unit  ->  Prims.bool = (fun uu____1718 -> (get_hide_uvar_nums ()))


let hint_info : Prims.unit  ->  Prims.bool = (fun uu____1721 -> (get_hint_info ()))


let indent : Prims.unit  ->  Prims.bool = (fun uu____1724 -> (get_indent ()))


let initial_fuel : Prims.unit  ->  Prims.int = (fun uu____1727 -> (get_initial_fuel ()))


let initial_ifuel : Prims.unit  ->  Prims.int = (fun uu____1730 -> (get_initial_ifuel ()))


let inline_arith : Prims.unit  ->  Prims.bool = (fun uu____1733 -> (get_inline_arith ()))


let interactive : Prims.unit  ->  Prims.bool = (fun uu____1736 -> (get_in ()))


let lax : Prims.unit  ->  Prims.bool = (fun uu____1739 -> (get_lax ()))


let log_queries : Prims.unit  ->  Prims.bool = (fun uu____1742 -> (get_log_queries ()))


let log_types : Prims.unit  ->  Prims.bool = (fun uu____1745 -> (get_log_types ()))


let max_fuel : Prims.unit  ->  Prims.int = (fun uu____1748 -> (get_max_fuel ()))


let max_ifuel : Prims.unit  ->  Prims.int = (fun uu____1751 -> (get_max_ifuel ()))


let min_fuel : Prims.unit  ->  Prims.int = (fun uu____1754 -> (get_min_fuel ()))


let ml_ish : Prims.unit  ->  Prims.bool = (fun uu____1757 -> (get_MLish ()))


let n_cores : Prims.unit  ->  Prims.int = (fun uu____1760 -> (get_n_cores ()))


let no_default_includes : Prims.unit  ->  Prims.bool = (fun uu____1763 -> (get_no_default_includes ()))


let no_extract : Prims.string  ->  Prims.bool = (fun s -> (let _0_100 = (get_no_extract ())
in (FStar_All.pipe_right _0_100 (FStar_List.contains s))))


let no_location_info : Prims.unit  ->  Prims.bool = (fun uu____1770 -> (get_no_location_info ()))


let norm_then_print : Prims.unit  ->  Prims.bool = (fun uu____1773 -> (let _0_101 = (get_print_before_norm ())
in (_0_101 = false)))


let output_dir : Prims.unit  ->  Prims.string Prims.option = (fun uu____1777 -> (get_odir ()))


let print_bound_var_types : Prims.unit  ->  Prims.bool = (fun uu____1780 -> (get_print_bound_var_types ()))


let print_effect_args : Prims.unit  ->  Prims.bool = (fun uu____1783 -> (get_print_effect_args ()))


let print_fuels : Prims.unit  ->  Prims.bool = (fun uu____1786 -> (get_print_fuels ()))


let print_implicits : Prims.unit  ->  Prims.bool = (fun uu____1789 -> (get_print_implicits ()))


let print_real_names : Prims.unit  ->  Prims.bool = (fun uu____1792 -> (get_prn ()))


let print_universes : Prims.unit  ->  Prims.bool = (fun uu____1795 -> (get_print_universes ()))


let print_z3_statistics : Prims.unit  ->  Prims.bool = (fun uu____1798 -> (get_print_z3_statistics ()))


let record_hints : Prims.unit  ->  Prims.bool = (fun uu____1801 -> (get_record_hints ()))


let reuse_hint_for : Prims.unit  ->  Prims.string Prims.option = (fun uu____1805 -> (get_reuse_hint_for ()))


let silent : Prims.unit  ->  Prims.bool = (fun uu____1808 -> (get_silent ()))


let split_cases : Prims.unit  ->  Prims.int = (fun uu____1811 -> (get_split_cases ()))


let timing : Prims.unit  ->  Prims.bool = (fun uu____1814 -> (get_timing ()))


let trace_error : Prims.unit  ->  Prims.bool = (fun uu____1817 -> (get_trace_error ()))


let unthrottle_inductives : Prims.unit  ->  Prims.bool = (fun uu____1820 -> (get_unthrottle_inductives ()))


let use_eq_at_higher_order : Prims.unit  ->  Prims.bool = (fun uu____1823 -> (get_use_eq_at_higher_order ()))


let use_hints : Prims.unit  ->  Prims.bool = (fun uu____1826 -> (get_use_hints ()))


let verify_all : Prims.unit  ->  Prims.bool = (fun uu____1829 -> (get_verify_all ()))


let verify_module : Prims.unit  ->  Prims.string Prims.list = (fun uu____1833 -> (get_verify_module ()))


let warn_cardinality : Prims.unit  ->  Prims.bool = (fun uu____1836 -> (let _0_102 = (get_cardinality ())
in (_0_102 = "warn")))


let warn_top_level_effects : Prims.unit  ->  Prims.bool = (fun uu____1839 -> (get_warn_top_level_effects ()))


let z3_exe : Prims.unit  ->  Prims.string = (fun uu____1842 -> (

let uu____1843 = (get_smt ())
in (match (uu____1843) with
| None -> begin
(FStar_Platform.exe "z3")
end
| Some (s) -> begin
s
end)))


let z3_refresh : Prims.unit  ->  Prims.bool = (fun uu____1848 -> (get_z3refresh ()))


let z3_rlimit : Prims.unit  ->  Prims.int = (fun uu____1851 -> (get_z3rlimit ()))


let z3_seed : Prims.unit  ->  Prims.int = (fun uu____1854 -> (get_z3seed ()))


let z3_timeout : Prims.unit  ->  Prims.int = (fun uu____1857 -> (get_z3timeout ()))


let should_extract : Prims.string  ->  Prims.bool = (fun m -> ((not ((no_extract m))) && ((extract_all ()) || (

let uu____1861 = (get_extract_module ())
in (match (uu____1861) with
| [] -> begin
(

let uu____1863 = (get_extract_namespace ())
in (match (uu____1863) with
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




