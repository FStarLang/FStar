
open Prims

type debug_level_t =
| Low
| Medium
| High
| Extreme
| Other of Prims.string


let is_Low = (fun _discr_ -> (match (_discr_) with
| Low (_) -> begin
true
end
| _ -> begin
false
end))


let is_Medium = (fun _discr_ -> (match (_discr_) with
| Medium (_) -> begin
true
end
| _ -> begin
false
end))


let is_High = (fun _discr_ -> (match (_discr_) with
| High (_) -> begin
true
end
| _ -> begin
false
end))


let is_Extreme = (fun _discr_ -> (match (_discr_) with
| Extreme (_) -> begin
true
end
| _ -> begin
false
end))


let is_Other = (fun _discr_ -> (match (_discr_) with
| Other (_) -> begin
true
end
| _ -> begin
false
end))


let ___Other____0 = (fun projectee -> (match (projectee) with
| Other (_25_10) -> begin
_25_10
end))


type option_val =
| Bool of Prims.bool
| String of Prims.string
| Int of Prims.int
| List of option_val Prims.list
| Unset


let is_Bool = (fun _discr_ -> (match (_discr_) with
| Bool (_) -> begin
true
end
| _ -> begin
false
end))


let is_String = (fun _discr_ -> (match (_discr_) with
| String (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int = (fun _discr_ -> (match (_discr_) with
| Int (_) -> begin
true
end
| _ -> begin
false
end))


let is_List = (fun _discr_ -> (match (_discr_) with
| List (_) -> begin
true
end
| _ -> begin
false
end))


let is_Unset = (fun _discr_ -> (match (_discr_) with
| Unset (_) -> begin
true
end
| _ -> begin
false
end))


let ___Bool____0 = (fun projectee -> (match (projectee) with
| Bool (_25_13) -> begin
_25_13
end))


let ___String____0 = (fun projectee -> (match (projectee) with
| String (_25_16) -> begin
_25_16
end))


let ___Int____0 = (fun projectee -> (match (projectee) with
| Int (_25_19) -> begin
_25_19
end))


let ___List____0 = (fun projectee -> (match (projectee) with
| List (_25_22) -> begin
_25_22
end))


type options =
| Set
| Reset
| Restore


let is_Set = (fun _discr_ -> (match (_discr_) with
| Set (_) -> begin
true
end
| _ -> begin
false
end))


let is_Reset = (fun _discr_ -> (match (_discr_) with
| Reset (_) -> begin
true
end
| _ -> begin
false
end))


let is_Restore = (fun _discr_ -> (match (_discr_) with
| Restore (_) -> begin
true
end
| _ -> begin
false
end))


let __unit_tests__ : Prims.bool FStar_ST.ref = (FStar_Util.mk_ref false)


let __unit_tests : Prims.unit  ->  Prims.bool = (fun _25_23 -> (match (()) with
| () -> begin
(FStar_ST.read __unit_tests__)
end))


let __set_unit_tests : Prims.unit  ->  Prims.unit = (fun _25_24 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals __unit_tests__ true)
end))


let __clear_unit_tests : Prims.unit  ->  Prims.unit = (fun _25_25 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals __unit_tests__ false)
end))


let as_bool : option_val  ->  Prims.bool = (fun _25_1 -> (match (_25_1) with
| Bool (b) -> begin
b
end
| _25_30 -> begin
(failwith "Impos: expected Bool")
end))


let as_int : option_val  ->  Prims.int = (fun _25_2 -> (match (_25_2) with
| Int (b) -> begin
b
end
| _25_35 -> begin
(failwith "Impos: expected Int")
end))


let as_string : option_val  ->  Prims.string = (fun _25_3 -> (match (_25_3) with
| String (b) -> begin
b
end
| _25_40 -> begin
(failwith "Impos: expected String")
end))


let as_list = (fun as_t _25_4 -> (match (_25_4) with
| List (ts) -> begin
(FStar_All.pipe_right ts (FStar_List.map as_t))
end
| _25_46 -> begin
(failwith "Impos: expected List")
end))


let as_option = (fun as_t _25_5 -> (match (_25_5) with
| Unset -> begin
None
end
| v -> begin
(let _124_101 = (as_t v)
in Some (_124_101))
end))


let fstar_options : option_val FStar_Util.smap Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let peek : Prims.unit  ->  option_val FStar_Util.smap = (fun _25_51 -> (match (()) with
| () -> begin
(let _124_104 = (FStar_ST.read fstar_options)
in (FStar_List.hd _124_104))
end))


let pop : Prims.unit  ->  Prims.unit = (fun _25_52 -> (match (()) with
| () -> begin
(match ((FStar_ST.read fstar_options)) with
| ([]) | ((_)::[]) -> begin
(failwith "TOO MANY POPS!")
end
| (_25_59)::tl -> begin
(FStar_ST.op_Colon_Equals fstar_options tl)
end)
end))


let push : Prims.unit  ->  Prims.unit = (fun _25_61 -> (match (()) with
| () -> begin
(let _124_112 = (let _124_111 = (let _124_109 = (peek ())
in (FStar_Util.smap_copy _124_109))
in (let _124_110 = (FStar_ST.read fstar_options)
in (_124_111)::_124_110))
in (FStar_ST.op_Colon_Equals fstar_options _124_112))
end))


let set_option : Prims.string  ->  option_val  ->  Prims.unit = (fun k v -> (let _124_117 = (peek ())
in (FStar_Util.smap_add _124_117 k v)))


let set_option' : (Prims.string * option_val)  ->  Prims.unit = (fun _25_66 -> (match (_25_66) with
| (k, v) -> begin
(set_option k v)
end))


let init : Prims.unit  ->  Prims.unit = (fun _25_67 -> (match (()) with
| () -> begin
(

let vals = ((("__temp_no_proj"), (List ([]))))::((("_fstar_home"), (String (""))))::((("_include_path"), (List ([]))))::((("admit_smt_queries"), (Bool (false))))::((("cardinality"), (String ("off"))))::((("codegen"), (Unset)))::((("codegen-lib"), (List ([]))))::((("debug"), (List ([]))))::((("debug_level"), (List ([]))))::((("dep"), (Unset)))::((("detail_errors"), (Bool (false))))::((("doc"), (Bool (false))))::((("dump_module"), (List ([]))))::((("eager_inference"), (Bool (false))))::((("explicit_deps"), (Bool (false))))::((("extract_module"), (List ([]))))::((("extract_all"), (Bool (false))))::((("fs_typ_app"), (Bool (false))))::((("fsi"), (Bool (false))))::((("fstar_home"), (Unset)))::((("full_context_dependency"), (Bool (true))))::((("hide_genident_nums"), (Bool (false))))::((("hide_uvar_nums"), (Bool (false))))::((("hint_info"), (Bool (false))))::((("in"), (Bool (false))))::((("include"), (List ([]))))::((("indent"), (Bool (false))))::((("initial_fuel"), (Int ((Prims.parse_int "2")))))::((("initial_ifuel"), (Int ((Prims.parse_int "1")))))::((("inline_arith"), (Bool (false))))::((("lax"), (Bool (false))))::((("log_queries"), (Bool (false))))::((("log_types"), (Bool (false))))::((("max_fuel"), (Int ((Prims.parse_int "8")))))::((("max_ifuel"), (Int ((Prims.parse_int "2")))))::((("min_fuel"), (Int ((Prims.parse_int "1")))))::((("MLish"), (Bool (false))))::((("n_cores"), (Int ((Prims.parse_int "1")))))::((("no_default_includes"), (Bool (false))))::((("no_extract"), (List ([]))))::((("no_location_info"), (Bool (false))))::((("odir"), (Unset)))::((("prims"), (Unset)))::((("pretype"), (Bool (true))))::((("prims_ref"), (Unset)))::((("print_before_norm"), (Bool (false))))::((("print_bound_var_types"), (Bool (false))))::((("print_effect_args"), (Bool (false))))::((("print_fuels"), (Bool (false))))::((("print_implicits"), (Bool (false))))::((("print_universes"), (Bool (false))))::((("print_z3_statistics"), (Bool (false))))::((("prn"), (Bool (false))))::((("record_hints"), (Bool (false))))::((("reuse_hint_for"), (Unset)))::((("show_signatures"), (List ([]))))::((("silent"), (Bool (false))))::((("smt"), (Unset)))::((("split_cases"), (Int ((Prims.parse_int "0")))))::((("stratified"), (Bool (false))))::((("timing"), (Bool (false))))::((("trace_error"), (Bool (false))))::((("unthrottle_inductives"), (Bool (false))))::((("use_eq_at_higher_order"), (Bool (false))))::((("use_hints"), (Bool (false))))::((("verify"), (Bool (true))))::((("verify_all"), (Bool (false))))::((("verify_module"), (List ([]))))::((("no_warn_top_level_effects"), (Bool (true))))::((("z3refresh"), (Bool (false))))::((("z3rlimit"), (Int ((Prims.parse_int "5")))))::((("z3seed"), (Int ((Prims.parse_int "0")))))::((("z3timeout"), (Int ((Prims.parse_int "5")))))::[]
in (

let o = (peek ())
in (

let _25_70 = (FStar_Util.smap_clear o)
in (FStar_All.pipe_right vals (FStar_List.iter set_option')))))
end))


let clear : Prims.unit  ->  Prims.unit = (fun _25_72 -> (match (()) with
| () -> begin
(

let o = (FStar_Util.smap_create (Prims.parse_int "50"))
in (

let _25_74 = (FStar_ST.op_Colon_Equals fstar_options ((o)::[]))
in (init ())))
end))


let _run : Prims.unit = (clear ())


let lookup_opt = (fun s c -> (match ((let _124_129 = (peek ())
in (FStar_Util.smap_try_find _124_129 s))) with
| None -> begin
(failwith (Prims.strcat "Impossible: option " (Prims.strcat s " not found")))
end
| Some (s) -> begin
(c s)
end))


let get_admit_smt_queries : Prims.unit  ->  Prims.bool = (fun _25_81 -> (match (()) with
| () -> begin
(lookup_opt "admit_smt_queries" as_bool)
end))


let get_cardinality : Prims.unit  ->  Prims.string = (fun _25_82 -> (match (()) with
| () -> begin
(lookup_opt "cardinality" as_string)
end))


let get_codegen : Prims.unit  ->  Prims.string Prims.option = (fun _25_83 -> (match (()) with
| () -> begin
(lookup_opt "codegen" (as_option as_string))
end))


let get_codegen_lib : Prims.unit  ->  Prims.string Prims.list = (fun _25_84 -> (match (()) with
| () -> begin
(lookup_opt "codegen-lib" (as_list as_string))
end))


let get_debug : Prims.unit  ->  Prims.string Prims.list = (fun _25_85 -> (match (()) with
| () -> begin
(lookup_opt "debug" (as_list as_string))
end))


let get_debug_level : Prims.unit  ->  Prims.string Prims.list = (fun _25_86 -> (match (()) with
| () -> begin
(lookup_opt "debug_level" (as_list as_string))
end))


let get_dep : Prims.unit  ->  Prims.string Prims.option = (fun _25_87 -> (match (()) with
| () -> begin
(lookup_opt "dep" (as_option as_string))
end))


let get_detail_errors : Prims.unit  ->  Prims.bool = (fun _25_88 -> (match (()) with
| () -> begin
(lookup_opt "detail_errors" as_bool)
end))


let get_doc : Prims.unit  ->  Prims.bool = (fun _25_89 -> (match (()) with
| () -> begin
(lookup_opt "doc" as_bool)
end))


let get_dump_module : Prims.unit  ->  Prims.string Prims.list = (fun _25_90 -> (match (()) with
| () -> begin
(lookup_opt "dump_module" (as_list as_string))
end))


let get_eager_inference : Prims.unit  ->  Prims.bool = (fun _25_91 -> (match (()) with
| () -> begin
(lookup_opt "eager_inference" as_bool)
end))


let get_explicit_deps : Prims.unit  ->  Prims.bool = (fun _25_92 -> (match (()) with
| () -> begin
(lookup_opt "explicit_deps" as_bool)
end))


let get_extract_all : Prims.unit  ->  Prims.bool = (fun _25_93 -> (match (()) with
| () -> begin
(lookup_opt "extract_all" as_bool)
end))


let get_extract_module : Prims.unit  ->  Prims.string Prims.list = (fun _25_94 -> (match (()) with
| () -> begin
(lookup_opt "extract_module" (as_list as_string))
end))


let get_fs_typ_app : Prims.unit  ->  Prims.bool = (fun _25_95 -> (match (()) with
| () -> begin
(lookup_opt "fs_typ_app" as_bool)
end))


let get_fstar_home : Prims.unit  ->  Prims.string Prims.option = (fun _25_96 -> (match (()) with
| () -> begin
(lookup_opt "fstar_home" (as_option as_string))
end))


let get_hide_genident_nums : Prims.unit  ->  Prims.bool = (fun _25_97 -> (match (()) with
| () -> begin
(lookup_opt "hide_genident_nums" as_bool)
end))


let get_hide_uvar_nums : Prims.unit  ->  Prims.bool = (fun _25_98 -> (match (()) with
| () -> begin
(lookup_opt "hide_uvar_nums" as_bool)
end))


let get_hint_info : Prims.unit  ->  Prims.bool = (fun _25_99 -> (match (()) with
| () -> begin
(lookup_opt "hint_info" as_bool)
end))


let get_in : Prims.unit  ->  Prims.bool = (fun _25_100 -> (match (()) with
| () -> begin
(lookup_opt "in" as_bool)
end))


let get_include : Prims.unit  ->  Prims.string Prims.list = (fun _25_101 -> (match (()) with
| () -> begin
(lookup_opt "include" (as_list as_string))
end))


let get_indent : Prims.unit  ->  Prims.bool = (fun _25_102 -> (match (()) with
| () -> begin
(lookup_opt "indent" as_bool)
end))


let get_initial_fuel : Prims.unit  ->  Prims.int = (fun _25_103 -> (match (()) with
| () -> begin
(lookup_opt "initial_fuel" as_int)
end))


let get_initial_ifuel : Prims.unit  ->  Prims.int = (fun _25_104 -> (match (()) with
| () -> begin
(lookup_opt "initial_ifuel" as_int)
end))


let get_inline_arith : Prims.unit  ->  Prims.bool = (fun _25_105 -> (match (()) with
| () -> begin
(lookup_opt "inline_arith" as_bool)
end))


let get_lax : Prims.unit  ->  Prims.bool = (fun _25_106 -> (match (()) with
| () -> begin
(lookup_opt "lax" as_bool)
end))


let get_log_queries : Prims.unit  ->  Prims.bool = (fun _25_107 -> (match (()) with
| () -> begin
(lookup_opt "log_queries" as_bool)
end))


let get_log_types : Prims.unit  ->  Prims.bool = (fun _25_108 -> (match (()) with
| () -> begin
(lookup_opt "log_types" as_bool)
end))


let get_max_fuel : Prims.unit  ->  Prims.int = (fun _25_109 -> (match (()) with
| () -> begin
(lookup_opt "max_fuel" as_int)
end))


let get_max_ifuel : Prims.unit  ->  Prims.int = (fun _25_110 -> (match (()) with
| () -> begin
(lookup_opt "max_ifuel" as_int)
end))


let get_min_fuel : Prims.unit  ->  Prims.int = (fun _25_111 -> (match (()) with
| () -> begin
(lookup_opt "min_fuel" as_int)
end))


let get_MLish : Prims.unit  ->  Prims.bool = (fun _25_112 -> (match (()) with
| () -> begin
(lookup_opt "MLish" as_bool)
end))


let get_n_cores : Prims.unit  ->  Prims.int = (fun _25_113 -> (match (()) with
| () -> begin
(lookup_opt "n_cores" as_int)
end))


let get_no_default_includes : Prims.unit  ->  Prims.bool = (fun _25_114 -> (match (()) with
| () -> begin
(lookup_opt "no_default_includes" as_bool)
end))


let get_no_extract : Prims.unit  ->  Prims.string Prims.list = (fun _25_115 -> (match (()) with
| () -> begin
(lookup_opt "no_extract" (as_list as_string))
end))


let get_no_location_info : Prims.unit  ->  Prims.bool = (fun _25_116 -> (match (()) with
| () -> begin
(lookup_opt "no_location_info" as_bool)
end))


let get_odir : Prims.unit  ->  Prims.string Prims.option = (fun _25_117 -> (match (()) with
| () -> begin
(lookup_opt "odir" (as_option as_string))
end))


let get_prims : Prims.unit  ->  Prims.string Prims.option = (fun _25_118 -> (match (()) with
| () -> begin
(lookup_opt "prims" (as_option as_string))
end))


let get_print_before_norm : Prims.unit  ->  Prims.bool = (fun _25_119 -> (match (()) with
| () -> begin
(lookup_opt "print_before_norm" as_bool)
end))


let get_print_bound_var_types : Prims.unit  ->  Prims.bool = (fun _25_120 -> (match (()) with
| () -> begin
(lookup_opt "print_bound_var_types" as_bool)
end))


let get_print_effect_args : Prims.unit  ->  Prims.bool = (fun _25_121 -> (match (()) with
| () -> begin
(lookup_opt "print_effect_args" as_bool)
end))


let get_print_fuels : Prims.unit  ->  Prims.bool = (fun _25_122 -> (match (()) with
| () -> begin
(lookup_opt "print_fuels" as_bool)
end))


let get_print_implicits : Prims.unit  ->  Prims.bool = (fun _25_123 -> (match (()) with
| () -> begin
(lookup_opt "print_implicits" as_bool)
end))


let get_print_universes : Prims.unit  ->  Prims.bool = (fun _25_124 -> (match (()) with
| () -> begin
(lookup_opt "print_universes" as_bool)
end))


let get_print_z3_statistics : Prims.unit  ->  Prims.bool = (fun _25_125 -> (match (()) with
| () -> begin
(lookup_opt "print_z3_statistics" as_bool)
end))


let get_prn : Prims.unit  ->  Prims.bool = (fun _25_126 -> (match (()) with
| () -> begin
(lookup_opt "prn" as_bool)
end))


let get_record_hints : Prims.unit  ->  Prims.bool = (fun _25_127 -> (match (()) with
| () -> begin
(lookup_opt "record_hints" as_bool)
end))


let get_reuse_hint_for : Prims.unit  ->  Prims.string Prims.option = (fun _25_128 -> (match (()) with
| () -> begin
(lookup_opt "reuse_hint_for" (as_option as_string))
end))


let get_show_signatures : Prims.unit  ->  Prims.string Prims.list = (fun _25_129 -> (match (()) with
| () -> begin
(lookup_opt "show_signatures" (as_list as_string))
end))


let get_silent : Prims.unit  ->  Prims.bool = (fun _25_130 -> (match (()) with
| () -> begin
(lookup_opt "silent" as_bool)
end))


let get_smt : Prims.unit  ->  Prims.string Prims.option = (fun _25_131 -> (match (()) with
| () -> begin
(lookup_opt "smt" (as_option as_string))
end))


let get_split_cases : Prims.unit  ->  Prims.int = (fun _25_132 -> (match (()) with
| () -> begin
(lookup_opt "split_cases" as_int)
end))


let get_stratified : Prims.unit  ->  Prims.bool = (fun _25_133 -> (match (()) with
| () -> begin
(lookup_opt "stratified" as_bool)
end))


let get_timing : Prims.unit  ->  Prims.bool = (fun _25_134 -> (match (()) with
| () -> begin
(lookup_opt "timing" as_bool)
end))


let get_trace_error : Prims.unit  ->  Prims.bool = (fun _25_135 -> (match (()) with
| () -> begin
(lookup_opt "trace_error" as_bool)
end))


let get_unthrottle_inductives : Prims.unit  ->  Prims.bool = (fun _25_136 -> (match (()) with
| () -> begin
(lookup_opt "unthrottle_inductives" as_bool)
end))


let get_use_eq_at_higher_order : Prims.unit  ->  Prims.bool = (fun _25_137 -> (match (()) with
| () -> begin
(lookup_opt "use_eq_at_higher_order" as_bool)
end))


let get_use_hints : Prims.unit  ->  Prims.bool = (fun _25_138 -> (match (()) with
| () -> begin
(lookup_opt "use_hints" as_bool)
end))


let get_verify_all : Prims.unit  ->  Prims.bool = (fun _25_139 -> (match (()) with
| () -> begin
(lookup_opt "verify_all" as_bool)
end))


let get_verify_module : Prims.unit  ->  Prims.string Prims.list = (fun _25_140 -> (match (()) with
| () -> begin
(lookup_opt "verify_module" (as_list as_string))
end))


let get___temp_no_proj : Prims.unit  ->  Prims.string Prims.list = (fun _25_141 -> (match (()) with
| () -> begin
(lookup_opt "__temp_no_proj" (as_list as_string))
end))


let get_version : Prims.unit  ->  Prims.bool = (fun _25_142 -> (match (()) with
| () -> begin
(lookup_opt "version" as_bool)
end))


let get_warn_top_level_effects : Prims.unit  ->  Prims.bool = (fun _25_143 -> (match (()) with
| () -> begin
(lookup_opt "no_warn_top_level_effects" as_bool)
end))


let get_z3refresh : Prims.unit  ->  Prims.bool = (fun _25_144 -> (match (()) with
| () -> begin
(lookup_opt "z3refresh" as_bool)
end))


let get_z3rlimit : Prims.unit  ->  Prims.int = (fun _25_145 -> (match (()) with
| () -> begin
(lookup_opt "z3rlimit" as_int)
end))


let get_z3seed : Prims.unit  ->  Prims.int = (fun _25_146 -> (match (()) with
| () -> begin
(lookup_opt "z3seed" as_int)
end))


let get_z3timeout : Prims.unit  ->  Prims.int = (fun _25_147 -> (match (()) with
| () -> begin
(lookup_opt "z3timeout" as_int)
end))


let dlevel : Prims.string  ->  debug_level_t = (fun _25_6 -> (match (_25_6) with
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


let debug_level_geq : debug_level_t  ->  Prims.bool = (fun l2 -> (let _124_273 = (get_debug_level ())
in (FStar_All.pipe_right _124_273 (FStar_Util.for_some (fun l1 -> (one_debug_level_geq (dlevel l1) l2))))))


let include_path_base_dirs : Prims.string Prims.list = ("/lib")::("/lib/fstar")::[]


let universe_include_path_base_dirs : Prims.string Prims.list = ("/ulib")::("/lib/fstar")::[]


let display_version : Prims.unit  ->  Prims.unit = (fun _25_165 -> (match (()) with
| () -> begin
(let _124_276 = (FStar_Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" FStar_Version.version FStar_Version.platform FStar_Version.compiler FStar_Version.date FStar_Version.commit)
in (FStar_Util.print_string _124_276))
end))


let display_usage_aux = (fun specs -> (

let _25_167 = (FStar_Util.print_string "fstar.exe [options] file[s]\n")
in (FStar_List.iter (fun _25_174 -> (match (_25_174) with
| (_25_170, flag, p, doc) -> begin
(match (p) with
| FStar_Getopt.ZeroArgs (ig) -> begin
if (doc = "") then begin
(let _124_281 = (let _124_280 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format1 "  --%s\n" _124_280))
in (FStar_Util.print_string _124_281))
end else begin
(let _124_283 = (let _124_282 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format2 "  --%s  %s\n" _124_282 doc))
in (FStar_Util.print_string _124_283))
end
end
| FStar_Getopt.OneArg (_25_178, argname) -> begin
if (doc = "") then begin
(let _124_287 = (let _124_286 = (FStar_Util.colorize_bold flag)
in (let _124_285 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format2 "  --%s %s\n" _124_286 _124_285)))
in (FStar_Util.print_string _124_287))
end else begin
(let _124_290 = (let _124_289 = (FStar_Util.colorize_bold flag)
in (let _124_288 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format3 "  --%s %s  %s\n" _124_289 _124_288 doc)))
in (FStar_Util.print_string _124_290))
end
end)
end)) specs)))


let mk_spec : (FStar_Char.char * Prims.string * option_val FStar_Getopt.opt_variant * Prims.string)  ->  FStar_Getopt.opt = (fun o -> (

let _25_187 = o
in (match (_25_187) with
| (ns, name, arg, desc) -> begin
(

let arg = (match (arg) with
| FStar_Getopt.ZeroArgs (f) -> begin
(

let g = (fun _25_191 -> (match (()) with
| () -> begin
(let _124_297 = (let _124_296 = (f ())
in ((name), (_124_296)))
in (set_option' _124_297))
end))
in FStar_Getopt.ZeroArgs (g))
end
| FStar_Getopt.OneArg (f, d) -> begin
(

let g = (fun x -> (let _124_302 = (let _124_301 = (f x)
in ((name), (_124_301)))
in (set_option' _124_302)))
in FStar_Getopt.OneArg (((g), (d))))
end)
in ((ns), (name), (arg), (desc)))
end)))


let cons_extract_module : Prims.string  ->  option_val = (fun s -> (let _124_309 = (let _124_308 = (let _124_306 = (get_extract_module ())
in ((FStar_String.lowercase s))::_124_306)
in (FStar_All.pipe_right _124_308 (FStar_List.map (fun _124_307 -> String (_124_307)))))
in List (_124_309)))


let add_extract_module : Prims.string  ->  Prims.unit = (fun s -> (let _124_312 = (cons_extract_module s)
in (set_option "extract_module" _124_312)))


let cons_verify_module : Prims.string  ->  option_val = (fun s -> (let _124_318 = (let _124_317 = (let _124_315 = (get_verify_module ())
in ((FStar_String.lowercase s))::_124_315)
in (FStar_All.pipe_right _124_317 (FStar_List.map (fun _124_316 -> String (_124_316)))))
in List (_124_318)))


let add_verify_module : Prims.string  ->  Prims.unit = (fun s -> (let _124_321 = (cons_verify_module s)
in (set_option "verify_module" _124_321)))


let rec specs : Prims.unit  ->  FStar_Getopt.opt Prims.list = (fun _25_203 -> (match (()) with
| () -> begin
(

let specs = (((FStar_Getopt.noshort), ("admit_smt_queries"), (FStar_Getopt.OneArg ((((fun s -> if (s = "true") then begin
Bool (true)
end else begin
if (s = "false") then begin
Bool (false)
end else begin
(failwith "Invalid argument to --admit_smt_queries")
end
end)), ("[true|false]")))), ("Admit SMT queries, unsafe! (default \'false\')")))::(((FStar_Getopt.noshort), ("cardinality"), (FStar_Getopt.OneArg ((((fun x -> (let _124_332 = (validate_cardinality x)
in String (_124_332)))), ("[off|warn|check]")))), ("Check cardinality constraints on inductive data types (default \'off\')")))::(((FStar_Getopt.noshort), ("codegen"), (FStar_Getopt.OneArg ((((fun s -> (let _124_336 = (parse_codegen s)
in String (_124_336)))), ("[OCaml|FSharp|Kremlin]")))), ("Generate code for execution")))::(((FStar_Getopt.noshort), ("codegen-lib"), (FStar_Getopt.OneArg ((((fun s -> (let _124_343 = (let _124_342 = (let _124_340 = (get_codegen_lib ())
in (s)::_124_340)
in (FStar_All.pipe_right _124_342 (FStar_List.map (fun _124_341 -> String (_124_341)))))
in List (_124_343)))), ("[namespace]")))), ("External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")))::(((FStar_Getopt.noshort), ("debug"), (FStar_Getopt.OneArg ((((fun x -> (let _124_350 = (let _124_349 = (let _124_347 = (get_debug ())
in (x)::_124_347)
in (FStar_All.pipe_right _124_349 (FStar_List.map (fun _124_348 -> String (_124_348)))))
in List (_124_350)))), ("[module name]")))), ("Print lots of debugging information while checking module")))::(((FStar_Getopt.noshort), ("debug_level"), (FStar_Getopt.OneArg ((((fun x -> (let _124_357 = (let _124_356 = (let _124_354 = (get_debug_level ())
in (x)::_124_354)
in (FStar_All.pipe_right _124_356 (FStar_List.map (fun _124_355 -> String (_124_355)))))
in List (_124_357)))), ("[Low|Medium|High|Extreme|...]")))), ("Control the verbosity of debugging info")))::(((FStar_Getopt.noshort), ("dep"), (FStar_Getopt.OneArg ((((fun x -> if ((x = "make") || (x = "graph")) then begin
String (x)
end else begin
(failwith "invalid argument to \'dep\'")
end)), ("[make|graph]")))), ("Output the transitive closure of the dependency graph in a format suitable for the given tool")))::(((FStar_Getopt.noshort), ("detail_errors"), (FStar_Getopt.ZeroArgs ((fun _25_211 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1; incompatible with --stratified")))::(((FStar_Getopt.noshort), ("doc"), (FStar_Getopt.ZeroArgs ((fun _25_212 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")))::(((FStar_Getopt.noshort), ("dump_module"), (FStar_Getopt.OneArg ((((fun x -> (let _124_370 = (let _124_368 = (let _124_366 = (get_dump_module ())
in (x)::_124_366)
in (FStar_All.pipe_right _124_368 (FStar_List.map (fun _124_367 -> String (_124_367)))))
in (FStar_All.pipe_right _124_370 (fun _124_369 -> List (_124_369)))))), ("[module name]")))), ("")))::(((FStar_Getopt.noshort), ("eager_inference"), (FStar_Getopt.ZeroArgs ((fun _25_214 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Solve all type-inference constraints eagerly; more efficient but at the cost of generality")))::(((FStar_Getopt.noshort), ("explicit_deps"), (FStar_Getopt.ZeroArgs ((fun _25_215 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Do not find dependencies automatically, the user provides them on the command-line")))::(((FStar_Getopt.noshort), ("extract_all"), (FStar_Getopt.ZeroArgs ((fun _25_216 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Discover the complete dependency graph and do not stop at interface boundaries")))::(((FStar_Getopt.noshort), ("extract_module"), (FStar_Getopt.OneArg (((cons_extract_module), ("[module name]")))), ("Only extract the specified modules (instead of the possibly-partial dependency graph)")))::(((FStar_Getopt.noshort), ("fs_typ_app"), (FStar_Getopt.ZeroArgs ((fun _25_217 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Allow the use of t<t1,...,tn> syntax for type applications;\n        brittle since it clashes with the integer less-than operator")))::(((FStar_Getopt.noshort), ("fstar_home"), (FStar_Getopt.OneArg ((((fun _124_377 -> String (_124_377))), ("[dir]")))), ("Set the FSTAR_HOME variable to [dir]")))::(((FStar_Getopt.noshort), ("hide_genident_nums"), (FStar_Getopt.ZeroArgs ((fun _25_218 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Don\'t print generated identifier numbers")))::(((FStar_Getopt.noshort), ("hide_uvar_nums"), (FStar_Getopt.ZeroArgs ((fun _25_219 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Don\'t print unification variable numbers")))::(((FStar_Getopt.noshort), ("hint_info"), (FStar_Getopt.ZeroArgs ((fun _25_220 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Print information regarding hints")))::(((FStar_Getopt.noshort), ("in"), (FStar_Getopt.ZeroArgs ((fun _25_221 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Interactive mode; reads input from stdin")))::(((FStar_Getopt.noshort), ("include"), (FStar_Getopt.OneArg ((((fun s -> (let _124_388 = (let _124_387 = (let _124_385 = (get_include ())
in (FStar_List.append _124_385 ((s)::[])))
in (FStar_All.pipe_right _124_387 (FStar_List.map (fun _124_386 -> String (_124_386)))))
in List (_124_388)))), ("[path]")))), ("A directory in which to search for files included on the command line")))::(((FStar_Getopt.noshort), ("indent"), (FStar_Getopt.ZeroArgs ((fun _25_223 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Parses and outputs the files on the command line")))::(((FStar_Getopt.noshort), ("initial_fuel"), (FStar_Getopt.OneArg ((((fun x -> (let _124_393 = (FStar_Util.int_of_string x)
in Int (_124_393)))), ("[non-negative integer]")))), ("Number of unrolling of recursive functions to try initially (default 2)")))::(((FStar_Getopt.noshort), ("initial_ifuel"), (FStar_Getopt.OneArg ((((fun x -> (let _124_397 = (FStar_Util.int_of_string x)
in Int (_124_397)))), ("[non-negative integer]")))), ("Number of unrolling of inductive datatypes to try at first (default 1)")))::(((FStar_Getopt.noshort), ("inline_arith"), (FStar_Getopt.ZeroArgs ((fun _25_226 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Inline definitions of arithmetic functions in the SMT encoding")))::(((FStar_Getopt.noshort), ("lax"), (FStar_Getopt.ZeroArgs ((fun _25_227 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Run the lax-type checker only (admit all verification conditions)")))::(((FStar_Getopt.noshort), ("log_types"), (FStar_Getopt.ZeroArgs ((fun _25_228 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Print types computed for data/val/let-bindings")))::(((FStar_Getopt.noshort), ("log_queries"), (FStar_Getopt.ZeroArgs ((fun _25_229 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Log the Z3 queries in several queries-*.smt2 files, as we go")))::(((FStar_Getopt.noshort), ("max_fuel"), (FStar_Getopt.OneArg ((((fun x -> (let _124_405 = (FStar_Util.int_of_string x)
in Int (_124_405)))), ("[non-negative integer]")))), ("Number of unrolling of recursive functions to try at most (default 8)")))::(((FStar_Getopt.noshort), ("max_ifuel"), (FStar_Getopt.OneArg ((((fun x -> (let _124_409 = (FStar_Util.int_of_string x)
in Int (_124_409)))), ("[non-negative integer]")))), ("Number of unrolling of inductive datatypes to try at most (default 2)")))::(((FStar_Getopt.noshort), ("min_fuel"), (FStar_Getopt.OneArg ((((fun x -> (let _124_413 = (FStar_Util.int_of_string x)
in Int (_124_413)))), ("[non-negative integer]")))), ("Minimum number of unrolling of recursive functions to try (default 1)")))::(((FStar_Getopt.noshort), ("MLish"), (FStar_Getopt.ZeroArgs ((fun _25_233 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Introduce unification variables that are only dependent on the type variables in the context")))::(((FStar_Getopt.noshort), ("n_cores"), (FStar_Getopt.OneArg ((((fun x -> (let _124_418 = (FStar_Util.int_of_string x)
in Int (_124_418)))), ("[positive integer]")))), ("Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")))::(((FStar_Getopt.noshort), ("no_default_includes"), (FStar_Getopt.ZeroArgs ((fun _25_235 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Ignore the default module search paths")))::(((FStar_Getopt.noshort), ("no_extract"), (FStar_Getopt.OneArg ((((fun x -> (let _124_426 = (let _124_425 = (let _124_423 = (get_no_extract ())
in (x)::_124_423)
in (FStar_All.pipe_right _124_425 (FStar_List.map (fun _124_424 -> String (_124_424)))))
in List (_124_426)))), ("[module name]")))), ("Do not extract code from this module")))::(((FStar_Getopt.noshort), ("no_location_info"), (FStar_Getopt.ZeroArgs ((fun _25_237 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")))::(((FStar_Getopt.noshort), ("odir"), (FStar_Getopt.OneArg ((((fun _124_429 -> String (_124_429))), ("[dir]")))), ("Place output in directory [dir]")))::(((FStar_Getopt.noshort), ("prims"), (FStar_Getopt.OneArg ((((fun _124_431 -> String (_124_431))), ("file")))), ("")))::(((FStar_Getopt.noshort), ("print_before_norm"), (FStar_Getopt.ZeroArgs ((fun _25_238 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Do not normalize types before printing (for debugging)")))::(((FStar_Getopt.noshort), ("print_bound_var_types"), (FStar_Getopt.ZeroArgs ((fun _25_239 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Print the types of bound variables")))::(((FStar_Getopt.noshort), ("print_effect_args"), (FStar_Getopt.ZeroArgs ((fun _25_240 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Print inferred predicate transformers for all computation types")))::(((FStar_Getopt.noshort), ("print_fuels"), (FStar_Getopt.ZeroArgs ((fun _25_241 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Print the fuel amounts used for each successful query")))::(((FStar_Getopt.noshort), ("print_implicits"), (FStar_Getopt.ZeroArgs ((fun _25_242 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Print implicit arguments")))::(((FStar_Getopt.noshort), ("print_universes"), (FStar_Getopt.ZeroArgs ((fun _25_243 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Print universes")))::(((FStar_Getopt.noshort), ("print_z3_statistics"), (FStar_Getopt.ZeroArgs ((fun _25_244 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Print Z3 statistics for each SMT query")))::(((FStar_Getopt.noshort), ("prn"), (FStar_Getopt.ZeroArgs ((fun _25_245 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Print real names (you may want to use this in conjunction with log_queries)")))::(((FStar_Getopt.noshort), ("record_hints"), (FStar_Getopt.ZeroArgs ((fun _25_246 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Record a database of hints for efficient proof replay")))::(((FStar_Getopt.noshort), ("reuse_hint_for"), (FStar_Getopt.OneArg ((((fun _124_442 -> String (_124_442))), ("top-level name in the current module")))), ("Optimistically, attempt using the recorded hint for \'f\' when trying to verify some other term \'g\'")))::(((FStar_Getopt.noshort), ("show_signatures"), (FStar_Getopt.OneArg ((((fun x -> (let _124_449 = (let _124_448 = (let _124_446 = (get_show_signatures ())
in (x)::_124_446)
in (FStar_All.pipe_right _124_448 (FStar_List.map (fun _124_447 -> String (_124_447)))))
in List (_124_449)))), ("[module name]")))), ("Show the checked signatures for all top-level symbols in the module")))::(((FStar_Getopt.noshort), ("silent"), (FStar_Getopt.ZeroArgs ((fun _25_248 -> (match (()) with
| () -> begin
Bool (true)
end)))), (" ")))::(((FStar_Getopt.noshort), ("smt"), (FStar_Getopt.OneArg ((((fun _124_452 -> String (_124_452))), ("[path]")))), ("Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)")))::(((FStar_Getopt.noshort), ("split_cases"), (FStar_Getopt.OneArg ((((fun n -> (let _124_456 = (FStar_Util.int_of_string n)
in Int (_124_456)))), ("[positive integer]")))), ("Partition VC of a match into groups of [n] cases")))::(((FStar_Getopt.noshort), ("stratified"), (FStar_Getopt.ZeroArgs ((fun _25_250 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Remove the support for universes")))::(((FStar_Getopt.noshort), ("timing"), (FStar_Getopt.ZeroArgs ((fun _25_251 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Print the time it takes to verify each top-level definition")))::(((FStar_Getopt.noshort), ("trace_error"), (FStar_Getopt.ZeroArgs ((fun _25_252 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Don\'t print an error message; show an exception trace instead")))::(((FStar_Getopt.noshort), ("unthrottle_inductives"), (FStar_Getopt.ZeroArgs ((fun _25_253 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")))::(((FStar_Getopt.noshort), ("use_eq_at_higher_order"), (FStar_Getopt.ZeroArgs ((fun _25_254 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Use equality constraints when comparing higher-order types (Temporary)")))::(((FStar_Getopt.noshort), ("use_hints"), (FStar_Getopt.ZeroArgs ((fun _25_255 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("Use a previously recorded hints database for proof replay")))::(((FStar_Getopt.noshort), ("verify_all"), (FStar_Getopt.ZeroArgs ((fun _25_256 -> (match (()) with
| () -> begin
Bool (true)
end)))), ("With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.")))::(((FStar_Getopt.noshort), ("verify_module"), (FStar_Getopt.OneArg (((cons_verify_module), ("[module name]")))), ("Name of the module to verify")))::(((FStar_Getopt.noshort), ("__temp_no_proj"), (FStar_Getopt.OneArg ((((fun x -> (let _124_471 = (let _124_470 = (let _124_468 = (get___temp_no_proj ())
in (x)::_124_468)
in (FStar_All.pipe_right _124_470 (FStar_List.map (fun _124_469 -> String (_124_469)))))
in List (_124_471)))), ("[module name]")))), ("Don\'t generate projectors for this module")))::((('v'), ("version"), (FStar_Getopt.ZeroArgs ((fun _25_258 -> (

let _25_260 = (display_version ())
in (FStar_All.exit (Prims.parse_int "0")))))), ("Display version number")))::(((FStar_Getopt.noshort), ("no_warn_top_level_effects"), (FStar_Getopt.ZeroArgs ((fun _25_262 -> (match (()) with
| () -> begin
Bool (false)
end)))), ("Top-level effects are checked by default; turn this flag on to prevent warning when this happens")))::(((FStar_Getopt.noshort), ("z3refresh"), (FStar_Getopt.ZeroArgs ((fun _25_263 -> (match (()) with
| () -> begin
Bool (false)
end)))), ("Restart Z3 after each query; useful for ensuring proof robustness")))::(((FStar_Getopt.noshort), ("z3rlimit"), (FStar_Getopt.OneArg ((((fun s -> (let _124_478 = (FStar_Util.int_of_string s)
in Int (_124_478)))), ("[positive integer]")))), ("Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")))::(((FStar_Getopt.noshort), ("z3seed"), (FStar_Getopt.OneArg ((((fun s -> (let _124_482 = (FStar_Util.int_of_string s)
in Int (_124_482)))), ("[positive integer]")))), ("Set the Z3 random seed (default 0)")))::(((FStar_Getopt.noshort), ("z3timeout"), (FStar_Getopt.OneArg ((((fun s -> (

let _25_267 = (FStar_Util.print_string "Warning: z3timeout ignored with universes; use z3rlimit instead\n")
in (let _124_486 = (FStar_Util.int_of_string s)
in Int (_124_486))))), ("[positive integer]")))), ("Set the Z3 per-query (soft) timeout to [t] seconds (default 5)")))::[]
in (let _124_488 = (FStar_List.map mk_spec specs)
in ((('h'), ("help"), (FStar_Getopt.ZeroArgs ((fun x -> (

let _25_271 = (display_usage_aux specs)
in (FStar_All.exit (Prims.parse_int "0")))))), ("Display this information")))::_124_488))
end))
and parse_codegen : Prims.string  ->  Prims.string = (fun s -> (match (s) with
| ("Kremlin") | ("OCaml") | ("FSharp") -> begin
s
end
| _25_278 -> begin
(

let _25_279 = (FStar_Util.print_string "Wrong argument to codegen flag\n")
in (

let _25_281 = (let _124_490 = (specs ())
in (display_usage_aux _124_490))
in (FStar_All.exit (Prims.parse_int "1"))))
end))
and validate_cardinality : Prims.string  ->  Prims.string = (fun x -> (match (x) with
| ("warn") | ("check") | ("off") -> begin
x
end
| _25_288 -> begin
(

let _25_289 = (FStar_Util.print_string "Wrong argument to cardinality flag\n")
in (

let _25_291 = (let _124_492 = (specs ())
in (display_usage_aux _124_492))
in (FStar_All.exit (Prims.parse_int "1"))))
end))


let settable : Prims.string  ->  Prims.bool = (fun _25_7 -> (match (_25_7) with
| ("admit_smt_queries") | ("cardinality") | ("debug") | ("debug_level") | ("detail_errors") | ("eager_inference") | ("hide_genident_nums") | ("hide_uvar_nums") | ("hint_info") | ("initial_fuel") | ("initial_ifuel") | ("inline_arith") | ("lax") | ("log_types") | ("log_queries") | ("max_fuel") | ("max_ifuel") | ("min_fuel") | ("print_before_norm") | ("print_bound_var_types") | ("print_effect_args") | ("print_fuels") | ("print_implicits") | ("print_universes") | ("print_z3_statistics") | ("prn") | ("show_signatures") | ("silent") | ("split_cases") | ("timing") | ("trace_error") | ("unthrottle_inductives") | ("use_eq_at_higher_order") | ("__temp_no_proj") | ("no_warn_top_level_effects") | ("reuse_hint_for") | ("z3refresh") -> begin
true
end
| _25_332 -> begin
false
end))


let resettable : Prims.string  ->  Prims.bool = (fun s -> ((((settable s) || (s = "z3timeout")) || (s = "z3rlimit")) || (s = "z3seed")))


let all_specs : FStar_Getopt.opt Prims.list = (specs ())


let settable_specs : (FStar_Char.char * Prims.string * Prims.unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun _25_341 -> (match (_25_341) with
| (_25_335, x, _25_338, _25_340) -> begin
(settable x)
end))))


let resettable_specs : (FStar_Char.char * Prims.string * Prims.unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun _25_349 -> (match (_25_349) with
| (_25_343, x, _25_346, _25_348) -> begin
(resettable x)
end))))


let display_usage : Prims.unit  ->  Prims.unit = (fun _25_350 -> (match (()) with
| () -> begin
(let _124_501 = (specs ())
in (display_usage_aux _124_501))
end))


let fstar_home : Prims.unit  ->  Prims.string = (fun _25_351 -> (match (()) with
| () -> begin
(match ((get_fstar_home ())) with
| None -> begin
(

let x = (FStar_Util.get_exec_dir ())
in (

let x = (Prims.strcat x "/..")
in (

let _25_355 = (set_option' (("fstar_home"), (String (x))))
in x)))
end
| Some (x) -> begin
x
end)
end))


let set_options : options  ->  Prims.string  ->  FStar_Getopt.parse_cmdline_res = (fun o s -> (

let specs = (match (o) with
| Set -> begin
if (not ((get_stratified ()))) then begin
resettable_specs
end else begin
settable_specs
end
end
| Reset -> begin
resettable_specs
end
| Restore -> begin
all_specs
end)
in (FStar_Getopt.parse_string specs (fun _25_365 -> ()) s)))


let file_list_ : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let parse_cmd_line : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun _25_367 -> (match (()) with
| () -> begin
(

let res = (let _124_514 = (specs ())
in (FStar_Getopt.parse_cmdline _124_514 (fun i -> (let _124_513 = (let _124_512 = (FStar_ST.read file_list_)
in (FStar_List.append _124_512 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list_ _124_513)))))
in (let _124_515 = (FStar_ST.read file_list_)
in ((res), (_124_515))))
end))


let file_list : Prims.unit  ->  Prims.string Prims.list = (fun _25_370 -> (match (()) with
| () -> begin
(FStar_ST.read file_list_)
end))


let restore_cmd_line_options : Prims.bool  ->  FStar_Getopt.parse_cmdline_res = (fun should_clear -> (

let old_verify_module = (get_verify_module ())
in (

let _25_373 = if should_clear then begin
(clear ())
end else begin
(init ())
end
in (

let r = (let _124_521 = (specs ())
in (FStar_Getopt.parse_cmdline _124_521 (fun x -> ())))
in (

let _25_377 = (let _124_525 = (let _124_524 = (let _124_523 = (FStar_List.map (fun _124_522 -> String (_124_522)) old_verify_module)
in List (_124_523))
in (("verify_module"), (_124_524)))
in (set_option' _124_525))
in r)))))


let should_verify : Prims.string  ->  Prims.bool = (fun m -> if (get_lax ()) then begin
false
end else begin
if (get_verify_all ()) then begin
true
end else begin
(match ((get_verify_module ())) with
| [] -> begin
(let _124_531 = (file_list ())
in (FStar_List.existsML (fun f -> (

let f = (FStar_Util.basename f)
in (

let f = (let _124_530 = (((FStar_String.length f) - (let _124_529 = (FStar_Util.get_file_extension f)
in (FStar_String.length _124_529))) - (Prims.parse_int "1"))
in (FStar_String.substring f (Prims.parse_int "0") _124_530))
in ((FStar_String.lowercase f) = m)))) _124_531))
end
| l -> begin
(FStar_List.contains (FStar_String.lowercase m) l)
end)
end
end)


let dont_gen_projectors : Prims.string  ->  Prims.bool = (fun m -> (let _124_534 = (get___temp_no_proj ())
in (FStar_List.contains m _124_534)))


let should_print_message : Prims.string  ->  Prims.bool = (fun m -> if (should_verify m) then begin
(m <> "Prims")
end else begin
false
end)


let include_path : Prims.unit  ->  Prims.string Prims.list = (fun _25_387 -> (match (()) with
| () -> begin
if (get_no_default_includes ()) then begin
(get_include ())
end else begin
(

let h = (fstar_home ())
in (

let defs = if (not ((get_stratified ()))) then begin
universe_include_path_base_dirs
end else begin
include_path_base_dirs
end
in (let _124_543 = (let _124_540 = (FStar_All.pipe_right defs (FStar_List.map (fun x -> (Prims.strcat h x))))
in (FStar_All.pipe_right _124_540 (FStar_List.filter FStar_Util.file_exists)))
in (let _124_542 = (let _124_541 = (get_include ())
in (FStar_List.append _124_541 ((".")::[])))
in (FStar_List.append _124_543 _124_542)))))
end
end))


let find_file : Prims.string  ->  Prims.string Prims.option = (fun filename -> if (FStar_Util.is_path_absolute filename) then begin
if (FStar_Util.file_exists filename) then begin
Some (filename)
end else begin
None
end
end else begin
(let _124_548 = (let _124_546 = (include_path ())
in (FStar_List.rev _124_546))
in (FStar_Util.find_map _124_548 (fun p -> (

let path = (FStar_Util.join_paths p filename)
in if (FStar_Util.file_exists path) then begin
Some (path)
end else begin
None
end))))
end)


let prims : Prims.unit  ->  Prims.string = (fun _25_394 -> (match (()) with
| () -> begin
(match ((get_prims ())) with
| None -> begin
(

let filename = "prims.fst"
in (match ((find_file filename)) with
| Some (result) -> begin
result
end
| None -> begin
(let _124_552 = (let _124_551 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
in FStar_Util.Failure (_124_551))
in (Prims.raise _124_552))
end))
end
| Some (x) -> begin
x
end)
end))


let prepend_output_dir : Prims.string  ->  Prims.string = (fun fname -> (match ((get_odir ())) with
| None -> begin
fname
end
| Some (x) -> begin
(Prims.strcat x (Prims.strcat "/" fname))
end))


let __temp_no_proj : Prims.string  ->  Prims.bool = (fun s -> (let _124_557 = (get___temp_no_proj ())
in (FStar_All.pipe_right _124_557 (FStar_List.contains s))))


let admit_smt_queries : Prims.unit  ->  Prims.bool = (fun _25_407 -> (match (()) with
| () -> begin
(get_admit_smt_queries ())
end))


let check_cardinality : Prims.unit  ->  Prims.bool = (fun _25_408 -> (match (()) with
| () -> begin
((get_cardinality ()) = "check")
end))


let codegen : Prims.unit  ->  Prims.string Prims.option = (fun _25_409 -> (match (()) with
| () -> begin
(get_codegen ())
end))


let codegen_libs : Prims.unit  ->  Prims.string Prims.list Prims.list = (fun _25_410 -> (match (()) with
| () -> begin
(let _124_567 = (get_codegen_lib ())
in (FStar_All.pipe_right _124_567 (FStar_List.map (fun x -> (FStar_Util.split x ".")))))
end))


let debug_any : Prims.unit  ->  Prims.bool = (fun _25_412 -> (match (()) with
| () -> begin
((get_debug ()) <> [])
end))


let debug_at_level : Prims.string  ->  debug_level_t  ->  Prims.bool = (fun modul level -> (((modul = "") || (let _124_574 = (get_debug ())
in (FStar_All.pipe_right _124_574 (FStar_List.contains modul)))) && (debug_level_geq level)))


let dep : Prims.unit  ->  Prims.string Prims.option = (fun _25_415 -> (match (()) with
| () -> begin
(get_dep ())
end))


let detail_errors : Prims.unit  ->  Prims.bool = (fun _25_416 -> (match (()) with
| () -> begin
(get_detail_errors ())
end))


let doc : Prims.unit  ->  Prims.bool = (fun _25_417 -> (match (()) with
| () -> begin
(get_doc ())
end))


let dump_module : Prims.string  ->  Prims.bool = (fun s -> (let _124_583 = (get_dump_module ())
in (FStar_All.pipe_right _124_583 (FStar_List.contains s))))


let eager_inference : Prims.unit  ->  Prims.bool = (fun _25_419 -> (match (()) with
| () -> begin
(get_eager_inference ())
end))


let explicit_deps : Prims.unit  ->  Prims.bool = (fun _25_420 -> (match (()) with
| () -> begin
(get_explicit_deps ())
end))


let extract_all : Prims.unit  ->  Prims.bool = (fun _25_421 -> (match (()) with
| () -> begin
(get_extract_all ())
end))


let fs_typ_app : Prims.unit  ->  Prims.bool = (fun _25_422 -> (match (()) with
| () -> begin
(get_fs_typ_app ())
end))


let full_context_dependency : Prims.unit  ->  Prims.bool = (fun _25_423 -> (match (()) with
| () -> begin
((get_MLish ()) = false)
end))


let hide_genident_nums : Prims.unit  ->  Prims.bool = (fun _25_424 -> (match (()) with
| () -> begin
(get_hide_genident_nums ())
end))


let hide_uvar_nums : Prims.unit  ->  Prims.bool = (fun _25_425 -> (match (()) with
| () -> begin
(get_hide_uvar_nums ())
end))


let hint_info : Prims.unit  ->  Prims.bool = (fun _25_426 -> (match (()) with
| () -> begin
(get_hint_info ())
end))


let indent : Prims.unit  ->  Prims.bool = (fun _25_427 -> (match (()) with
| () -> begin
(get_indent ())
end))


let initial_fuel : Prims.unit  ->  Prims.int = (fun _25_428 -> (match (()) with
| () -> begin
(get_initial_fuel ())
end))


let initial_ifuel : Prims.unit  ->  Prims.int = (fun _25_429 -> (match (()) with
| () -> begin
(get_initial_ifuel ())
end))


let inline_arith : Prims.unit  ->  Prims.bool = (fun _25_430 -> (match (()) with
| () -> begin
(get_inline_arith ())
end))


let interactive : Prims.unit  ->  Prims.bool = (fun _25_431 -> (match (()) with
| () -> begin
(get_in ())
end))


let lax : Prims.unit  ->  Prims.bool = (fun _25_432 -> (match (()) with
| () -> begin
(get_lax ())
end))


let log_queries : Prims.unit  ->  Prims.bool = (fun _25_433 -> (match (()) with
| () -> begin
(get_log_queries ())
end))


let log_types : Prims.unit  ->  Prims.bool = (fun _25_434 -> (match (()) with
| () -> begin
(get_log_types ())
end))


let max_fuel : Prims.unit  ->  Prims.int = (fun _25_435 -> (match (()) with
| () -> begin
(get_max_fuel ())
end))


let max_ifuel : Prims.unit  ->  Prims.int = (fun _25_436 -> (match (()) with
| () -> begin
(get_max_ifuel ())
end))


let min_fuel : Prims.unit  ->  Prims.int = (fun _25_437 -> (match (()) with
| () -> begin
(get_min_fuel ())
end))


let ml_ish : Prims.unit  ->  Prims.bool = (fun _25_438 -> (match (()) with
| () -> begin
(get_MLish ())
end))


let n_cores : Prims.unit  ->  Prims.int = (fun _25_439 -> (match (()) with
| () -> begin
(get_n_cores ())
end))


let no_default_includes : Prims.unit  ->  Prims.bool = (fun _25_440 -> (match (()) with
| () -> begin
(get_no_default_includes ())
end))


let no_extract : Prims.string  ->  Prims.bool = (fun s -> (let _124_630 = (get_no_extract ())
in (FStar_All.pipe_right _124_630 (FStar_List.contains s))))


let no_location_info : Prims.unit  ->  Prims.bool = (fun _25_442 -> (match (()) with
| () -> begin
(get_no_location_info ())
end))


let norm_then_print : Prims.unit  ->  Prims.bool = (fun _25_443 -> (match (()) with
| () -> begin
((get_print_before_norm ()) = false)
end))


let output_dir : Prims.unit  ->  Prims.string Prims.option = (fun _25_444 -> (match (()) with
| () -> begin
(get_odir ())
end))


let print_bound_var_types : Prims.unit  ->  Prims.bool = (fun _25_445 -> (match (()) with
| () -> begin
(get_print_bound_var_types ())
end))


let print_effect_args : Prims.unit  ->  Prims.bool = (fun _25_446 -> (match (()) with
| () -> begin
(get_print_effect_args ())
end))


let print_fuels : Prims.unit  ->  Prims.bool = (fun _25_447 -> (match (()) with
| () -> begin
(get_print_fuels ())
end))


let print_implicits : Prims.unit  ->  Prims.bool = (fun _25_448 -> (match (()) with
| () -> begin
(get_print_implicits ())
end))


let print_real_names : Prims.unit  ->  Prims.bool = (fun _25_449 -> (match (()) with
| () -> begin
(get_prn ())
end))


let print_universes : Prims.unit  ->  Prims.bool = (fun _25_450 -> (match (()) with
| () -> begin
(get_print_universes ())
end))


let print_z3_statistics : Prims.unit  ->  Prims.bool = (fun _25_451 -> (match (()) with
| () -> begin
(get_print_z3_statistics ())
end))


let record_hints : Prims.unit  ->  Prims.bool = (fun _25_452 -> (match (()) with
| () -> begin
(get_record_hints ())
end))


let reuse_hint_for : Prims.unit  ->  Prims.string Prims.option = (fun _25_453 -> (match (()) with
| () -> begin
(get_reuse_hint_for ())
end))


let silent : Prims.unit  ->  Prims.bool = (fun _25_454 -> (match (()) with
| () -> begin
(get_silent ())
end))


let split_cases : Prims.unit  ->  Prims.int = (fun _25_455 -> (match (()) with
| () -> begin
(get_split_cases ())
end))


let timing : Prims.unit  ->  Prims.bool = (fun _25_456 -> (match (()) with
| () -> begin
(get_timing ())
end))


let trace_error : Prims.unit  ->  Prims.bool = (fun _25_457 -> (match (()) with
| () -> begin
(get_trace_error ())
end))


let universes : Prims.unit  ->  Prims.bool = (fun _25_458 -> (match (()) with
| () -> begin
(not ((get_stratified ())))
end))


let unthrottle_inductives : Prims.unit  ->  Prims.bool = (fun _25_459 -> (match (()) with
| () -> begin
(get_unthrottle_inductives ())
end))


let use_eq_at_higher_order : Prims.unit  ->  Prims.bool = (fun _25_460 -> (match (()) with
| () -> begin
(get_use_eq_at_higher_order ())
end))


let use_hints : Prims.unit  ->  Prims.bool = (fun _25_461 -> (match (()) with
| () -> begin
(get_use_hints ())
end))


let verify_all : Prims.unit  ->  Prims.bool = (fun _25_462 -> (match (()) with
| () -> begin
(get_verify_all ())
end))


let verify_module : Prims.unit  ->  Prims.string Prims.list = (fun _25_463 -> (match (()) with
| () -> begin
(get_verify_module ())
end))


let warn_cardinality : Prims.unit  ->  Prims.bool = (fun _25_464 -> (match (()) with
| () -> begin
((get_cardinality ()) = "warn")
end))


let warn_top_level_effects : Prims.unit  ->  Prims.bool = (fun _25_465 -> (match (()) with
| () -> begin
(get_warn_top_level_effects ())
end))


let z3_exe : Prims.unit  ->  Prims.string = (fun _25_466 -> (match (()) with
| () -> begin
(match ((get_smt ())) with
| None -> begin
(FStar_Platform.exe "z3")
end
| Some (s) -> begin
s
end)
end))


let z3_refresh : Prims.unit  ->  Prims.bool = (fun _25_470 -> (match (()) with
| () -> begin
(get_z3refresh ())
end))


let z3_rlimit : Prims.unit  ->  Prims.int = (fun _25_471 -> (match (()) with
| () -> begin
(get_z3rlimit ())
end))


let z3_seed : Prims.unit  ->  Prims.int = (fun _25_472 -> (match (()) with
| () -> begin
(get_z3seed ())
end))


let z3_timeout : Prims.unit  ->  Prims.int = (fun _25_473 -> (match (()) with
| () -> begin
(get_z3timeout ())
end))


let should_extract : Prims.string  ->  Prims.bool = (fun m -> ((not ((no_extract m))) && ((extract_all ()) || (match ((get_extract_module ())) with
| [] -> begin
true
end
| l -> begin
(FStar_List.contains (FStar_String.lowercase m) l)
end))))




