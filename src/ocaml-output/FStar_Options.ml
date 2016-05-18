
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
| Other (_24_10) -> begin
_24_10
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
| Bool (_24_13) -> begin
_24_13
end))


let ___String____0 = (fun projectee -> (match (projectee) with
| String (_24_16) -> begin
_24_16
end))


let ___Int____0 = (fun projectee -> (match (projectee) with
| Int (_24_19) -> begin
_24_19
end))


let ___List____0 = (fun projectee -> (match (projectee) with
| List (_24_22) -> begin
_24_22
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


let __unit_tests : Prims.unit  ->  Prims.bool = (fun _24_23 -> (match (()) with
| () -> begin
(FStar_ST.read __unit_tests__)
end))


let __set_unit_tests : Prims.unit  ->  Prims.unit = (fun _24_24 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals __unit_tests__ true)
end))


let __clear_unit_tests : Prims.unit  ->  Prims.unit = (fun _24_25 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals __unit_tests__ false)
end))


let as_bool : option_val  ->  Prims.bool = (fun _24_1 -> (match (_24_1) with
| Bool (b) -> begin
b
end
| _24_30 -> begin
(FStar_All.failwith "Impos: expected Bool")
end))


let as_int : option_val  ->  Prims.int = (fun _24_2 -> (match (_24_2) with
| Int (b) -> begin
b
end
| _24_35 -> begin
(FStar_All.failwith "Impos: expected Int")
end))


let as_string : option_val  ->  Prims.string = (fun _24_3 -> (match (_24_3) with
| String (b) -> begin
b
end
| _24_40 -> begin
(FStar_All.failwith "Impos: expected String")
end))


let as_list = (fun as_t _24_4 -> (match (_24_4) with
| List (ts) -> begin
(FStar_All.pipe_right ts (FStar_List.map as_t))
end
| _24_46 -> begin
(FStar_All.failwith "Impos: expected List")
end))


let as_option = (fun as_t _24_5 -> (match (_24_5) with
| Unset -> begin
None
end
| v -> begin
(let _113_101 = (as_t v)
in Some (_113_101))
end))


let fstar_options : option_val FStar_Util.smap Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let peek : Prims.unit  ->  option_val FStar_Util.smap = (fun _24_51 -> (match (()) with
| () -> begin
(let _113_104 = (FStar_ST.read fstar_options)
in (FStar_List.hd _113_104))
end))


let pop : Prims.unit  ->  Prims.unit = (fun _24_52 -> (match (()) with
| () -> begin
(match ((FStar_ST.read fstar_options)) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "TOO MANY POPS!")
end
| _24_59::tl -> begin
(FStar_ST.op_Colon_Equals fstar_options tl)
end)
end))


let push : Prims.unit  ->  Prims.unit = (fun _24_61 -> (match (()) with
| () -> begin
(let _113_112 = (let _113_111 = (let _113_109 = (peek ())
in (FStar_Util.smap_copy _113_109))
in (let _113_110 = (FStar_ST.read fstar_options)
in (_113_111)::_113_110))
in (FStar_ST.op_Colon_Equals fstar_options _113_112))
end))


let set_option : Prims.string  ->  option_val  ->  Prims.unit = (fun k v -> (let _113_117 = (peek ())
in (FStar_Util.smap_add _113_117 k v)))


let set_option' : (Prims.string * option_val)  ->  Prims.unit = (fun _24_66 -> (match (_24_66) with
| (k, v) -> begin
(set_option k v)
end))


let init : Prims.unit  ->  Prims.unit = (fun _24_67 -> (match (()) with
| () -> begin
(

let vals = (("__temp_no_proj", List ([])))::(("_fstar_home", String ("")))::(("_include_path", List ([])))::(("admit_smt_queries", Bool (false)))::(("cardinality", String ("off")))::(("codegen", Unset))::(("codegen-lib", List ([])))::(("debug", List ([])))::(("debug_level", List ([])))::(("dep", Unset))::(("detail_errors", Bool (false)))::(("dump_module", List ([])))::(("eager_inference", Bool (false)))::(("explicit_deps", Bool (false)))::(("fs_typ_app", Bool (false)))::(("fsi", Bool (false)))::(("fstar_home", Unset))::(("full_context_dependency", Bool (true)))::(("hide_genident_nums", Bool (false)))::(("hide_uvar_nums", Bool (false)))::(("in", Bool (false)))::(("include", List ([])))::(("initial_fuel", Int (2)))::(("initial_ifuel", Int (1)))::(("inline_arith", Bool (false)))::(("lax", Bool (false)))::(("log_queries", Bool (false)))::(("log_types", Bool (false)))::(("max_fuel", Int (8)))::(("max_ifuel", Int (2)))::(("min_fuel", Int (1)))::(("MLish", Bool (false)))::(("n_cores", Int (1)))::(("no_default_includes", Bool (false)))::(("no_extract", List ([])))::(("no_location_info", Bool (true)))::(("odir", Unset))::(("prims", Unset))::(("pretype", Bool (true)))::(("prims_ref", Unset))::(("print_before_norm", Bool (false)))::(("print_bound_var_types", Bool (false)))::(("print_effect_args", Bool (false)))::(("print_fuels", Bool (false)))::(("print_implicits", Bool (false)))::(("print_universes", Bool (false)))::(("prn", Bool (false)))::(("show_signatures", List ([])))::(("silent", Bool (false)))::(("smt", Unset))::(("split_cases", Int (0)))::(("timing", Bool (false)))::(("trace_error", Bool (false)))::(("universes", Bool (false)))::(("unthrottle_inductives", Bool (false)))::(("use_eq_at_higher_order", Bool (false)))::(("use_native_int", Bool (false)))::(("verify", Bool (true)))::(("verify_module", List ([])))::(("warn_top_level_effects", Bool (false)))::(("z3timeout", Int (5)))::[]
in (

let o = (peek ())
in (

let _24_70 = (FStar_Util.smap_clear o)
in (FStar_All.pipe_right vals (FStar_List.iter set_option')))))
end))


let clear : Prims.unit  ->  Prims.unit = (fun _24_72 -> (match (()) with
| () -> begin
(

let o = (FStar_Util.smap_create 50)
in (

let _24_74 = (FStar_ST.op_Colon_Equals fstar_options ((o)::[]))
in (init ())))
end))


let _run : Prims.unit = (clear ())


let lookup_opt = (fun s c -> (match ((let _113_129 = (peek ())
in (FStar_Util.smap_try_find _113_129 s))) with
| None -> begin
(FStar_All.failwith (Prims.strcat (Prims.strcat "Impossible: option " s) " not found"))
end
| Some (s) -> begin
(c s)
end))


let get_admit_smt_queries : Prims.unit  ->  Prims.bool = (fun _24_81 -> (match (()) with
| () -> begin
(lookup_opt "admit_smt_queries" as_bool)
end))


let get_cardinality : Prims.unit  ->  Prims.string = (fun _24_82 -> (match (()) with
| () -> begin
(lookup_opt "cardinality" as_string)
end))


let get_codegen : Prims.unit  ->  Prims.string Prims.option = (fun _24_83 -> (match (()) with
| () -> begin
(lookup_opt "codegen" (as_option as_string))
end))


let get_codegen_lib : Prims.unit  ->  Prims.string Prims.list = (fun _24_84 -> (match (()) with
| () -> begin
(lookup_opt "codegen-lib" (as_list as_string))
end))


let get_debug : Prims.unit  ->  Prims.string Prims.list = (fun _24_85 -> (match (()) with
| () -> begin
(lookup_opt "debug" (as_list as_string))
end))


let get_debug_level : Prims.unit  ->  Prims.string Prims.list = (fun _24_86 -> (match (()) with
| () -> begin
(lookup_opt "debug_level" (as_list as_string))
end))


let get_dep : Prims.unit  ->  Prims.string Prims.option = (fun _24_87 -> (match (()) with
| () -> begin
(lookup_opt "dep" (as_option as_string))
end))


let get_detail_errors : Prims.unit  ->  Prims.bool = (fun _24_88 -> (match (()) with
| () -> begin
(lookup_opt "detail_errors" as_bool)
end))


let get_dump_module : Prims.unit  ->  Prims.string Prims.list = (fun _24_89 -> (match (()) with
| () -> begin
(lookup_opt "dump_module" (as_list as_string))
end))


let get_eager_inference : Prims.unit  ->  Prims.bool = (fun _24_90 -> (match (()) with
| () -> begin
(lookup_opt "eager_inference" as_bool)
end))


let get_explicit_deps : Prims.unit  ->  Prims.bool = (fun _24_91 -> (match (()) with
| () -> begin
(lookup_opt "explicit_deps" as_bool)
end))


let get_fs_typ_app : Prims.unit  ->  Prims.bool = (fun _24_92 -> (match (()) with
| () -> begin
(lookup_opt "fs_typ_app" as_bool)
end))


let get_fsi : Prims.unit  ->  Prims.bool = (fun _24_93 -> (match (()) with
| () -> begin
(lookup_opt "fsi" as_bool)
end))


let get_fstar_home : Prims.unit  ->  Prims.string Prims.option = (fun _24_94 -> (match (()) with
| () -> begin
(lookup_opt "fstar_home" (as_option as_string))
end))


let get_hide_genident_nums : Prims.unit  ->  Prims.bool = (fun _24_95 -> (match (()) with
| () -> begin
(lookup_opt "hide_genident_nums" as_bool)
end))


let get_hide_uvar_nums : Prims.unit  ->  Prims.bool = (fun _24_96 -> (match (()) with
| () -> begin
(lookup_opt "hide_uvar_nums" as_bool)
end))


let get_in : Prims.unit  ->  Prims.bool = (fun _24_97 -> (match (()) with
| () -> begin
(lookup_opt "in" as_bool)
end))


let get_include : Prims.unit  ->  Prims.string Prims.list = (fun _24_98 -> (match (()) with
| () -> begin
(lookup_opt "include" (as_list as_string))
end))


let get_initial_fuel : Prims.unit  ->  Prims.int = (fun _24_99 -> (match (()) with
| () -> begin
(lookup_opt "initial_fuel" as_int)
end))


let get_initial_ifuel : Prims.unit  ->  Prims.int = (fun _24_100 -> (match (()) with
| () -> begin
(lookup_opt "initial_ifuel" as_int)
end))


let get_inline_arith : Prims.unit  ->  Prims.bool = (fun _24_101 -> (match (()) with
| () -> begin
(lookup_opt "inline_arith" as_bool)
end))


let get_lax : Prims.unit  ->  Prims.bool = (fun _24_102 -> (match (()) with
| () -> begin
(lookup_opt "lax" as_bool)
end))


let get_log_queries : Prims.unit  ->  Prims.bool = (fun _24_103 -> (match (()) with
| () -> begin
(lookup_opt "log_queries" as_bool)
end))


let get_log_types : Prims.unit  ->  Prims.bool = (fun _24_104 -> (match (()) with
| () -> begin
(lookup_opt "log_types" as_bool)
end))


let get_max_fuel : Prims.unit  ->  Prims.int = (fun _24_105 -> (match (()) with
| () -> begin
(lookup_opt "max_fuel" as_int)
end))


let get_max_ifuel : Prims.unit  ->  Prims.int = (fun _24_106 -> (match (()) with
| () -> begin
(lookup_opt "max_ifuel" as_int)
end))


let get_min_fuel : Prims.unit  ->  Prims.int = (fun _24_107 -> (match (()) with
| () -> begin
(lookup_opt "min_fuel" as_int)
end))


let get_MLish : Prims.unit  ->  Prims.bool = (fun _24_108 -> (match (()) with
| () -> begin
(lookup_opt "MLish" as_bool)
end))


let get_n_cores : Prims.unit  ->  Prims.int = (fun _24_109 -> (match (()) with
| () -> begin
(lookup_opt "n_cores" as_int)
end))


let get_no_default_includes : Prims.unit  ->  Prims.bool = (fun _24_110 -> (match (()) with
| () -> begin
(lookup_opt "no_default_includes" as_bool)
end))


let get_no_extract : Prims.unit  ->  Prims.string Prims.list = (fun _24_111 -> (match (()) with
| () -> begin
(lookup_opt "no_extract" (as_list as_string))
end))


let get_no_location_info : Prims.unit  ->  Prims.bool = (fun _24_112 -> (match (()) with
| () -> begin
(lookup_opt "no_location_info" as_bool)
end))


let get_odir : Prims.unit  ->  Prims.string Prims.option = (fun _24_113 -> (match (()) with
| () -> begin
(lookup_opt "odir" (as_option as_string))
end))


let get_prims : Prims.unit  ->  Prims.string Prims.option = (fun _24_114 -> (match (()) with
| () -> begin
(lookup_opt "prims" (as_option as_string))
end))


let get_print_before_norm : Prims.unit  ->  Prims.bool = (fun _24_115 -> (match (()) with
| () -> begin
(lookup_opt "print_before_norm" as_bool)
end))


let get_print_bound_var_types : Prims.unit  ->  Prims.bool = (fun _24_116 -> (match (()) with
| () -> begin
(lookup_opt "print_bound_var_types" as_bool)
end))


let get_print_effect_args : Prims.unit  ->  Prims.bool = (fun _24_117 -> (match (()) with
| () -> begin
(lookup_opt "print_effect_args" as_bool)
end))


let get_print_fuels : Prims.unit  ->  Prims.bool = (fun _24_118 -> (match (()) with
| () -> begin
(lookup_opt "print_fuels" as_bool)
end))


let get_print_implicits : Prims.unit  ->  Prims.bool = (fun _24_119 -> (match (()) with
| () -> begin
(lookup_opt "print_implicits" as_bool)
end))


let get_print_universes : Prims.unit  ->  Prims.bool = (fun _24_120 -> (match (()) with
| () -> begin
(lookup_opt "print_universes" as_bool)
end))


let get_prn : Prims.unit  ->  Prims.bool = (fun _24_121 -> (match (()) with
| () -> begin
(lookup_opt "prn" as_bool)
end))


let get_show_signatures : Prims.unit  ->  Prims.string Prims.list = (fun _24_122 -> (match (()) with
| () -> begin
(lookup_opt "show_signatures" (as_list as_string))
end))


let get_silent : Prims.unit  ->  Prims.bool = (fun _24_123 -> (match (()) with
| () -> begin
(lookup_opt "silent" as_bool)
end))


let get_smt : Prims.unit  ->  Prims.string Prims.option = (fun _24_124 -> (match (()) with
| () -> begin
(lookup_opt "smt" (as_option as_string))
end))


let get_split_cases : Prims.unit  ->  Prims.int = (fun _24_125 -> (match (()) with
| () -> begin
(lookup_opt "split_cases" as_int)
end))


let get_timing : Prims.unit  ->  Prims.bool = (fun _24_126 -> (match (()) with
| () -> begin
(lookup_opt "timing" as_bool)
end))


let get_trace_error : Prims.unit  ->  Prims.bool = (fun _24_127 -> (match (()) with
| () -> begin
(lookup_opt "trace_error" as_bool)
end))


let get_universes : Prims.unit  ->  Prims.bool = (fun _24_128 -> (match (()) with
| () -> begin
(lookup_opt "universes" as_bool)
end))


let get_unthrottle_inductives : Prims.unit  ->  Prims.bool = (fun _24_129 -> (match (()) with
| () -> begin
(lookup_opt "unthrottle_inductives" as_bool)
end))


let get_use_eq_at_higher_order : Prims.unit  ->  Prims.bool = (fun _24_130 -> (match (()) with
| () -> begin
(lookup_opt "use_eq_at_higher_order" as_bool)
end))


let get_use_native_int : Prims.unit  ->  Prims.bool = (fun _24_131 -> (match (()) with
| () -> begin
(lookup_opt "use_native_int" as_bool)
end))


let get_verify_module : Prims.unit  ->  Prims.string Prims.list = (fun _24_132 -> (match (()) with
| () -> begin
(lookup_opt "verify_module" (as_list as_string))
end))


let get___temp_no_proj : Prims.unit  ->  Prims.string Prims.list = (fun _24_133 -> (match (()) with
| () -> begin
(lookup_opt "__temp_no_proj" (as_list as_string))
end))


let get_version : Prims.unit  ->  Prims.bool = (fun _24_134 -> (match (()) with
| () -> begin
(lookup_opt "version" as_bool)
end))


let get_warn_top_level_effects : Prims.unit  ->  Prims.bool = (fun _24_135 -> (match (()) with
| () -> begin
(lookup_opt "warn_top_level_effects" as_bool)
end))


let get_z3timeout : Prims.unit  ->  Prims.int = (fun _24_136 -> (match (()) with
| () -> begin
(lookup_opt "z3timeout" as_int)
end))


let dlevel : Prims.string  ->  debug_level_t = (fun _24_6 -> (match (_24_6) with
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


let debug_level_geq : debug_level_t  ->  Prims.bool = (fun l2 -> (let _113_251 = (get_debug_level ())
in (FStar_All.pipe_right _113_251 (FStar_Util.for_some (fun l1 -> (one_debug_level_geq (dlevel l1) l2))))))


let include_path_base_dirs : Prims.string Prims.list = ("/lib")::("/lib/fstar")::("/stdlib")::("/stdlib/fstar")::[]


let universe_include_path_base_dirs : Prims.string Prims.list = ("/ulib")::[]


let display_version : Prims.unit  ->  Prims.unit = (fun _24_154 -> (match (()) with
| () -> begin
(let _113_254 = (FStar_Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" FStar_Version.version FStar_Version.platform FStar_Version.compiler FStar_Version.date FStar_Version.commit)
in (FStar_Util.print_string _113_254))
end))


let display_usage_aux = (fun specs -> (

let _24_156 = (FStar_Util.print_string "fstar [option] file...\n")
in (FStar_List.iter (fun _24_163 -> (match (_24_163) with
| (_24_159, flag, p, doc) -> begin
(match (p) with
| FStar_Getopt.ZeroArgs (ig) -> begin
if (doc = "") then begin
(let _113_259 = (let _113_258 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format1 "  --%s\n" _113_258))
in (FStar_Util.print_string _113_259))
end else begin
(let _113_261 = (let _113_260 = (FStar_Util.colorize_bold flag)
in (FStar_Util.format2 "  --%s  %s\n" _113_260 doc))
in (FStar_Util.print_string _113_261))
end
end
| FStar_Getopt.OneArg (_24_167, argname) -> begin
if (doc = "") then begin
(let _113_265 = (let _113_264 = (FStar_Util.colorize_bold flag)
in (let _113_263 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format2 "  --%s %s\n" _113_264 _113_263)))
in (FStar_Util.print_string _113_265))
end else begin
(let _113_268 = (let _113_267 = (FStar_Util.colorize_bold flag)
in (let _113_266 = (FStar_Util.colorize_bold argname)
in (FStar_Util.format3 "  --%s %s  %s\n" _113_267 _113_266 doc)))
in (FStar_Util.print_string _113_268))
end
end)
end)) specs)))


let mk_spec : (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant * Prims.string)  ->  FStar_Getopt.opt = (fun o -> (

let _24_176 = o
in (match (_24_176) with
| (ns, name, arg, desc) -> begin
(

let arg = (match (arg) with
| FStar_Getopt.ZeroArgs (f) -> begin
(

let g = (fun _24_180 -> (match (()) with
| () -> begin
(let _113_275 = (let _113_274 = (f ())
in (name, _113_274))
in (set_option' _113_275))
end))
in FStar_Getopt.ZeroArgs (g))
end
| FStar_Getopt.OneArg (f, d) -> begin
(

let g = (fun x -> (let _113_280 = (let _113_279 = (f x)
in (name, _113_279))
in (set_option' _113_280)))
in FStar_Getopt.OneArg ((g, d)))
end)
in (ns, name, arg, desc))
end)))


let cons_verify_module : Prims.string  ->  option_val = (fun s -> (let _113_287 = (let _113_286 = (let _113_284 = (get_verify_module ())
in ((FStar_String.lowercase s))::_113_284)
in (FStar_All.pipe_right _113_286 (FStar_List.map (fun _113_285 -> String (_113_285)))))
in List (_113_287)))


let add_verify_module : Prims.string  ->  Prims.unit = (fun s -> (let _113_290 = (cons_verify_module s)
in (set_option "verify_module" _113_290)))


let rec specs : Prims.unit  ->  FStar_Getopt.opt Prims.list = (fun _24_190 -> (match (()) with
| () -> begin
(

let specs = ((FStar_Getopt.noshort, "admit_smt_queries", FStar_Getopt.OneArg (((fun s -> if (s = "true") then begin
Bool (true)
end else begin
if (s = "false") then begin
Bool (false)
end else begin
(FStar_All.failwith "Invalid argument to --admit_smt_queries")
end
end), "true|false")), "Admit SMT queries (UNSAFE! But, useful during development); default: \'false\'"))::((FStar_Getopt.noshort, "cardinality", FStar_Getopt.OneArg (((fun x -> (let _113_302 = (validate_cardinality x)
in String (_113_302))), "off|warn|check")), "Check cardinality constraints on inductive data types (default \'off\')"))::((FStar_Getopt.noshort, "codegen", FStar_Getopt.OneArg (((fun s -> (let _113_306 = (parse_codegen s)
in String (_113_306))), "OCaml|FSharp")), "Generate code for execution"))::((FStar_Getopt.noshort, "codegen-lib", FStar_Getopt.OneArg (((fun s -> (let _113_313 = (let _113_312 = (let _113_310 = (get_codegen_lib ())
in (s)::_113_310)
in (FStar_All.pipe_right _113_312 (FStar_List.map (fun _113_311 -> String (_113_311)))))
in List (_113_313))), "namespace")), "External runtime library library"))::((FStar_Getopt.noshort, "debug", FStar_Getopt.OneArg (((fun x -> (let _113_320 = (let _113_319 = (let _113_317 = (get_debug ())
in (x)::_113_317)
in (FStar_All.pipe_right _113_319 (FStar_List.map (fun _113_318 -> String (_113_318)))))
in List (_113_320))), "module name")), "Print LOTS of debugging information while checking module [arg]"))::((FStar_Getopt.noshort, "debug_level", FStar_Getopt.OneArg (((fun x -> (let _113_327 = (let _113_326 = (let _113_324 = (get_debug_level ())
in (x)::_113_324)
in (FStar_All.pipe_right _113_326 (FStar_List.map (fun _113_325 -> String (_113_325)))))
in List (_113_327))), "Low|Medium|High|Extreme|...")), "Control the verbosity of debugging info"))::((FStar_Getopt.noshort, "dep", FStar_Getopt.OneArg (((fun x -> if ((x = "make") || (x = "graph")) then begin
String (x)
end else begin
(FStar_All.failwith "invalid argument to \'dep\'")
end), "make|graph")), "Output the transitive closure of the dependency graph in a format suitable for the given tool"))::((FStar_Getopt.noshort, "detail_errors", FStar_Getopt.ZeroArgs ((fun _24_198 -> (match (()) with
| () -> begin
Bool (true)
end))), "Emit a detailed error report by asking the SMT solver many queries; will take longer; implies n_cores=1; requires --universes"))::((FStar_Getopt.noshort, "dump_module", FStar_Getopt.OneArg (((fun x -> (let _113_339 = (let _113_337 = (let _113_335 = (get_dump_module ())
in (x)::_113_335)
in (FStar_All.pipe_right _113_337 (FStar_List.map (fun _113_336 -> String (_113_336)))))
in (FStar_All.pipe_right _113_339 (fun _113_338 -> List (_113_338))))), "module name")), ""))::((FStar_Getopt.noshort, "eager_inference", FStar_Getopt.ZeroArgs ((fun _24_200 -> (match (()) with
| () -> begin
Bool (true)
end))), "Solve all type-inference constraints eagerly; more efficient but at the cost of generality"))::((FStar_Getopt.noshort, "explicit_deps", FStar_Getopt.ZeroArgs ((fun _24_201 -> (match (()) with
| () -> begin
Bool (true)
end))), "tell FStar to not find dependencies automatically because the user provides them on the command-line"))::((FStar_Getopt.noshort, "fs_typ_app", FStar_Getopt.ZeroArgs ((fun _24_202 -> (match (()) with
| () -> begin
Bool (true)
end))), "Allow the use of t<t1, \n       ..., \n       tn> syntax for type applications; brittle since it clashes with the integer less-than operator"))::((FStar_Getopt.noshort, "fsi", FStar_Getopt.ZeroArgs ((fun _24_203 -> (match (()) with
| () -> begin
Bool (true)
end))), "fsi flag; A flag to indicate if type checking a fsi in the interactive mode"))::((FStar_Getopt.noshort, "fstar_home", FStar_Getopt.OneArg (((fun _113_345 -> String (_113_345)), "dir")), "Set the FSTAR_HOME variable to dir"))::((FStar_Getopt.noshort, "hide_genident_nums", FStar_Getopt.ZeroArgs ((fun _24_204 -> (match (()) with
| () -> begin
Bool (true)
end))), "Don\'t print generated identifier numbers"))::((FStar_Getopt.noshort, "hide_uvar_nums", FStar_Getopt.ZeroArgs ((fun _24_205 -> (match (()) with
| () -> begin
Bool (true)
end))), "Don\'t print unification variable numbers"))::((FStar_Getopt.noshort, "in", FStar_Getopt.ZeroArgs ((fun _24_206 -> (match (()) with
| () -> begin
Bool (true)
end))), "Interactive mode; reads input from stdin"))::((FStar_Getopt.noshort, "include", FStar_Getopt.OneArg (((fun s -> (let _113_355 = (let _113_354 = (let _113_352 = (get_include ())
in (FStar_List.append _113_352 ((s)::[])))
in (FStar_All.pipe_right _113_354 (FStar_List.map (fun _113_353 -> String (_113_353)))))
in List (_113_355))), "path")), "A directory in which to search for files included on the command line"))::((FStar_Getopt.noshort, "initial_fuel", FStar_Getopt.OneArg (((fun x -> (let _113_359 = (FStar_Util.int_of_string x)
in Int (_113_359))), "non-negative integer")), "Number of unrolling of recursive functions to try initially (default 2)"))::((FStar_Getopt.noshort, "initial_ifuel", FStar_Getopt.OneArg (((fun x -> (let _113_363 = (FStar_Util.int_of_string x)
in Int (_113_363))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at first (default 1)"))::((FStar_Getopt.noshort, "inline_arith", FStar_Getopt.ZeroArgs ((fun _24_210 -> (match (()) with
| () -> begin
Bool (true)
end))), "Inline definitions of arithmetic functions in the SMT encoding"))::((FStar_Getopt.noshort, "lax", FStar_Getopt.ZeroArgs ((fun _24_211 -> (match (()) with
| () -> begin
Bool (true)
end))), "Run the lax-type checker only (admit all verification conditions)"))::((FStar_Getopt.noshort, "log_types", FStar_Getopt.ZeroArgs ((fun _24_212 -> (match (()) with
| () -> begin
Bool (true)
end))), "Print types computed for data/val/let-bindings"))::((FStar_Getopt.noshort, "log_queries", FStar_Getopt.ZeroArgs ((fun _24_213 -> (match (()) with
| () -> begin
Bool (true)
end))), "Log the Z3 queries in queries.smt2"))::((FStar_Getopt.noshort, "max_fuel", FStar_Getopt.OneArg (((fun x -> (let _113_371 = (FStar_Util.int_of_string x)
in Int (_113_371))), "non-negative integer")), "Number of unrolling of recursive functions to try at most (default 8)"))::((FStar_Getopt.noshort, "max_ifuel", FStar_Getopt.OneArg (((fun x -> (let _113_375 = (FStar_Util.int_of_string x)
in Int (_113_375))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at most (default 2)"))::((FStar_Getopt.noshort, "min_fuel", FStar_Getopt.OneArg (((fun x -> (let _113_379 = (FStar_Util.int_of_string x)
in Int (_113_379))), "non-negative integer")), "Minimum number of unrolling of recursive functions to try (default 1)"))::((FStar_Getopt.noshort, "MLish", FStar_Getopt.ZeroArgs ((fun _24_217 -> (match (()) with
| () -> begin
Bool (true)
end))), "Introduce unification variables that are only dependent on the type variables in the context"))::((FStar_Getopt.noshort, "n_cores", FStar_Getopt.OneArg (((fun x -> (let _113_384 = (FStar_Util.int_of_string x)
in Int (_113_384))), "positive integer")), "Maximum number of cores to use for the solver (default 1); implied detail_errors = false"))::((FStar_Getopt.noshort, "no_default_includes", FStar_Getopt.ZeroArgs ((fun _24_219 -> (match (()) with
| () -> begin
Bool (true)
end))), "Ignore the default module search paths"))::((FStar_Getopt.noshort, "no_extract", FStar_Getopt.OneArg (((fun x -> (let _113_392 = (let _113_391 = (let _113_389 = (get_no_extract ())
in (x)::_113_389)
in (FStar_All.pipe_right _113_391 (FStar_List.map (fun _113_390 -> String (_113_390)))))
in List (_113_392))), "module name")), "Do not extract code from this module"))::((FStar_Getopt.noshort, "no_location_info", FStar_Getopt.ZeroArgs ((fun _24_221 -> (match (()) with
| () -> begin
Bool (true)
end))), "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)"))::((FStar_Getopt.noshort, "odir", FStar_Getopt.OneArg (((fun _113_395 -> String (_113_395)), "dir")), "Place output in directory dir"))::((FStar_Getopt.noshort, "prims", FStar_Getopt.OneArg (((fun _113_397 -> String (_113_397)), "file")), ""))::((FStar_Getopt.noshort, "print_before_norm", FStar_Getopt.ZeroArgs ((fun _24_222 -> (match (()) with
| () -> begin
Bool (true)
end))), "Do not normalize types before printing (for debugging)"))::((FStar_Getopt.noshort, "print_bound_var_types", FStar_Getopt.ZeroArgs ((fun _24_223 -> (match (()) with
| () -> begin
Bool (true)
end))), "Print the types of bound variables"))::((FStar_Getopt.noshort, "print_effect_args", FStar_Getopt.ZeroArgs ((fun _24_224 -> (match (()) with
| () -> begin
Bool (true)
end))), "Print inferred predicate transformers for all computation types"))::((FStar_Getopt.noshort, "print_fuels", FStar_Getopt.ZeroArgs ((fun _24_225 -> (match (()) with
| () -> begin
Bool (true)
end))), "Print the fuel amounts used for each successful query"))::((FStar_Getopt.noshort, "print_implicits", FStar_Getopt.ZeroArgs ((fun _24_226 -> (match (()) with
| () -> begin
Bool (true)
end))), "Print implicit arguments"))::((FStar_Getopt.noshort, "print_universes", FStar_Getopt.ZeroArgs ((fun _24_227 -> (match (()) with
| () -> begin
Bool (true)
end))), "Print universes"))::((FStar_Getopt.noshort, "prn", FStar_Getopt.ZeroArgs ((fun _24_228 -> (match (()) with
| () -> begin
Bool (true)
end))), "Print real names---you may want to use this in conjunction with log_queries"))::((FStar_Getopt.noshort, "show_signatures", FStar_Getopt.OneArg (((fun x -> (let _113_411 = (let _113_410 = (let _113_408 = (get_show_signatures ())
in (x)::_113_408)
in (FStar_All.pipe_right _113_410 (FStar_List.map (fun _113_409 -> String (_113_409)))))
in List (_113_411))), "module name")), "Show the checked signatures for all top-level symbols in the module"))::((FStar_Getopt.noshort, "silent", FStar_Getopt.ZeroArgs ((fun _24_230 -> (match (()) with
| () -> begin
Bool (true)
end))), " "))::((FStar_Getopt.noshort, "smt", FStar_Getopt.OneArg (((fun _113_414 -> String (_113_414)), "path")), "Path to the SMT solver (usually Z3, \n        but could be any SMT2-compatible solver)"))::((FStar_Getopt.noshort, "split_cases", FStar_Getopt.OneArg (((fun n -> (let _113_418 = (FStar_Util.int_of_string n)
in Int (_113_418))), "positive integer, n")), "Partition VC of a match into groups of n cases"))::((FStar_Getopt.noshort, "timing", FStar_Getopt.ZeroArgs ((fun _24_232 -> (match (()) with
| () -> begin
Bool (true)
end))), "Print the time it takes to verify each top-level definition"))::((FStar_Getopt.noshort, "trace_error", FStar_Getopt.ZeroArgs ((fun _24_233 -> (match (()) with
| () -> begin
Bool (true)
end))), "Don\'t print an error message; show an exception trace instead"))::((FStar_Getopt.noshort, "universes", FStar_Getopt.ZeroArgs ((fun _24_234 -> (match (()) with
| () -> begin
Bool (true)
end))), "Use the (experimental) support for universes"))::((FStar_Getopt.noshort, "unthrottle_inductives", FStar_Getopt.ZeroArgs ((fun _24_235 -> (match (()) with
| () -> begin
Bool (true)
end))), "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)"))::((FStar_Getopt.noshort, "use_eq_at_higher_order", FStar_Getopt.ZeroArgs ((fun _24_236 -> (match (()) with
| () -> begin
Bool (true)
end))), "Use equality constraints when comparing higher-order types; temporary"))::((FStar_Getopt.noshort, "use_native_int", FStar_Getopt.ZeroArgs ((fun _24_237 -> (match (()) with
| () -> begin
Bool (true)
end))), "Extract the \'int\' type to platform-specific native int; you will need to link the generated code with the appropriate version of the prims library"))::((FStar_Getopt.noshort, "verify_module", FStar_Getopt.OneArg ((cons_verify_module, "string")), "Name of the module to verify"))::((FStar_Getopt.noshort, "__temp_no_proj", FStar_Getopt.OneArg (((fun x -> (let _113_432 = (let _113_431 = (let _113_429 = (get___temp_no_proj ())
in (x)::_113_429)
in (FStar_All.pipe_right _113_431 (FStar_List.map (fun _113_430 -> String (_113_430)))))
in List (_113_432))), "string")), "Don\'t generate projectors for this module"))::(('v', "version", FStar_Getopt.ZeroArgs ((fun _24_239 -> (

let _24_241 = (display_version ())
in (FStar_All.exit 0)))), "Display version number"))::((FStar_Getopt.noshort, "warn_top_level_effects", FStar_Getopt.ZeroArgs ((fun _24_243 -> (match (()) with
| () -> begin
Bool (true)
end))), "Top-level effects are ignored, \n        by default; turn this flag on to be warned when this happens"))::((FStar_Getopt.noshort, "z3timeout", FStar_Getopt.OneArg (((fun s -> (let _113_438 = (FStar_Util.int_of_string s)
in Int (_113_438))), "positive integer, t")), "Set the Z3 per-query (soft) timeout to t seconds (default 5)"))::[]
in (let _113_440 = (FStar_List.map mk_spec specs)
in (('h', "help", FStar_Getopt.ZeroArgs ((fun x -> (

let _24_247 = (display_usage_aux specs)
in (FStar_All.exit 0)))), "Display this information"))::_113_440))
end))
and parse_codegen : Prims.string  ->  Prims.string = (fun s -> (match (s) with
| ("OCaml") | ("FSharp") -> begin
s
end
| _24_253 -> begin
(

let _24_254 = (FStar_Util.print_string "Wrong argument to codegen flag\n")
in (

let _24_256 = (let _113_442 = (specs ())
in (display_usage_aux _113_442))
in (FStar_All.exit 1)))
end))
and validate_cardinality : Prims.string  ->  Prims.string = (fun x -> (match (x) with
| ("warn") | ("check") | ("off") -> begin
x
end
| _24_263 -> begin
(

let _24_264 = (FStar_Util.print_string "Wrong argument to cardinality flag\n")
in (

let _24_266 = (let _113_444 = (specs ())
in (display_usage_aux _113_444))
in (FStar_All.exit 1)))
end))
and set_interactive_fsi = (fun _24_268 -> if (get_in ()) then begin
(set_option' ("fsi", Bool (true)))
end else begin
(

let _24_270 = (FStar_Util.print_string "Set interactive flag first before setting interactive fsi flag\n")
in (

let _24_272 = (let _113_445 = (specs ())
in (display_usage_aux _113_445))
in (FStar_All.exit 1)))
end)


let settable : Prims.string  ->  Prims.bool = (fun _24_7 -> (match (_24_7) with
| ("admit_smt_queries") | ("cardinality") | ("debug") | ("debug_level") | ("detail_errors") | ("eager_inference") | ("hide_genident_nums") | ("hide_uvar_nums") | ("initial_fuel") | ("initial_ifuel") | ("inline_arith") | ("lax") | ("log_types") | ("log_queries") | ("max_fuel") | ("max_ifuel") | ("min_fuel") | ("print_before_norm") | ("print_bound_var_types") | ("print_effect_args") | ("print_fuels") | ("print_implicits") | ("print_universes") | ("prn") | ("show_signatures") | ("silent") | ("split_cases") | ("timing") | ("trace_error") | ("unthrottle_inductives") | ("use_eq_at_higher_order") | ("__temp_no_proj") | ("warn_top_level_effects") -> begin
true
end
| _24_309 -> begin
false
end))


let resettable : Prims.string  ->  Prims.bool = (fun s -> ((settable s) || (s = "z3timeout")))


let all_specs : FStar_Getopt.opt Prims.list = (specs ())


let settable_specs : (FStar_Char.char * Prims.string * Prims.unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun _24_318 -> (match (_24_318) with
| (_24_312, x, _24_315, _24_317) -> begin
(settable x)
end))))


let resettable_specs : (FStar_Char.char * Prims.string * Prims.unit FStar_Getopt.opt_variant * Prims.string) Prims.list = (FStar_All.pipe_right all_specs (FStar_List.filter (fun _24_326 -> (match (_24_326) with
| (_24_320, x, _24_323, _24_325) -> begin
(resettable x)
end))))


let display_usage : Prims.unit  ->  Prims.unit = (fun _24_327 -> (match (()) with
| () -> begin
(let _113_454 = (specs ())
in (display_usage_aux _113_454))
end))


let fstar_home : Prims.unit  ->  Prims.string = (fun _24_328 -> (match (()) with
| () -> begin
(match ((get_fstar_home ())) with
| None -> begin
(

let x = (FStar_Util.get_exec_dir ())
in (

let x = (Prims.strcat x "/..")
in (

let _24_332 = (set_option' ("fstar_home", String (x)))
in x)))
end
| Some (x) -> begin
x
end)
end))


let set_options : options  ->  Prims.string  ->  FStar_Getopt.parse_cmdline_res = (fun o s -> (

let specs = (match (o) with
| Set -> begin
settable_specs
end
| Reset -> begin
resettable_specs
end
| Restore -> begin
all_specs
end)
in (FStar_Getopt.parse_string specs (fun _24_342 -> ()) s)))


let parse_cmd_line : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun _24_344 -> (match (()) with
| () -> begin
(

let file_list = (FStar_Util.mk_ref [])
in (

let res = (let _113_467 = (specs ())
in (FStar_Getopt.parse_cmdline _113_467 (fun i -> (let _113_466 = (let _113_465 = (FStar_ST.read file_list)
in (FStar_List.append _113_465 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list _113_466)))))
in (let _113_468 = (FStar_ST.read file_list)
in (res, _113_468))))
end))


let restore_cmd_line_options : Prims.bool  ->  FStar_Getopt.parse_cmdline_res = (fun should_clear -> (

let old_verify_module = (get_verify_module ())
in (

let _24_350 = if should_clear then begin
(clear ())
end else begin
(init ())
end
in (

let r = (let _113_472 = (specs ())
in (FStar_Getopt.parse_cmdline _113_472 (fun x -> ())))
in (

let _24_354 = (let _113_476 = (let _113_475 = (let _113_474 = (FStar_List.map (fun _113_473 -> String (_113_473)) old_verify_module)
in List (_113_474))
in ("verify_module", _113_475))
in (set_option' _113_476))
in r)))))


let should_verify : Prims.string  ->  Prims.bool = (fun m -> if (get_lax ()) then begin
false
end else begin
(match ((get_verify_module ())) with
| [] -> begin
true
end
| l -> begin
(FStar_List.contains (FStar_String.lowercase m) l)
end)
end)


let dont_gen_projectors : Prims.string  ->  Prims.bool = (fun m -> (let _113_481 = (get___temp_no_proj ())
in (FStar_List.contains m _113_481)))


let should_print_message : Prims.string  ->  Prims.bool = (fun m -> if (should_verify m) then begin
(m <> "Prims")
end else begin
false
end)


let include_path : Prims.unit  ->  Prims.string Prims.list = (fun _24_361 -> (match (()) with
| () -> begin
if (get_no_default_includes ()) then begin
(get_include ())
end else begin
(

let h = (fstar_home ())
in (

let defs = if (get_universes ()) then begin
universe_include_path_base_dirs
end else begin
include_path_base_dirs
end
in (let _113_490 = (let _113_489 = (let _113_487 = (FStar_All.pipe_right defs (FStar_List.map (fun x -> (Prims.strcat h x))))
in (FStar_All.pipe_right _113_487 (FStar_List.filter FStar_Util.file_exists)))
in (let _113_488 = (get_include ())
in (FStar_List.append _113_489 _113_488)))
in (FStar_List.append _113_490 ((".")::[])))))
end
end))


let find_file : Prims.string  ->  Prims.string Prims.option = (fun filename -> (

let search_path = (include_path ())
in try
(match (()) with
| () -> begin
(let _113_495 = if (FStar_Util.is_path_absolute filename) then begin
if (FStar_Util.file_exists filename) then begin
Some (filename)
end else begin
None
end
end else begin
(FStar_Util.find_map search_path (fun p -> (

let path = (FStar_Util.join_paths p filename)
in if (FStar_Util.file_exists path) then begin
Some (path)
end else begin
None
end)))
end
in (FStar_Util.map_option FStar_Util.normalize_file_path _113_495))
end)
with
| _24_371 -> begin
None
end))


let prims : Prims.unit  ->  Prims.string = (fun _24_376 -> (match (()) with
| () -> begin
(match ((get_prims ())) with
| None -> begin
(

let filen = "prims.fst"
in (match ((find_file filen)) with
| Some (result) -> begin
result
end
| None -> begin
(let _113_500 = (let _113_499 = (FStar_Util.format1 "unable to find required file \"%s\" in the module search path.\n" filen)
in FStar_Util.Failure (_113_499))
in (Prims.raise _113_500))
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
(Prims.strcat (Prims.strcat x "/") fname)
end))


let __temp_no_proj : Prims.string  ->  Prims.bool = (fun s -> (let _113_505 = (get___temp_no_proj ())
in (FStar_All.pipe_right _113_505 (FStar_List.contains s))))


let admit_smt_queries : Prims.unit  ->  Prims.bool = (fun _24_389 -> (match (()) with
| () -> begin
(get_admit_smt_queries ())
end))


let check_cardinality : Prims.unit  ->  Prims.bool = (fun _24_390 -> (match (()) with
| () -> begin
((get_cardinality ()) = "check")
end))


let codegen : Prims.unit  ->  Prims.string Prims.option = (fun _24_391 -> (match (()) with
| () -> begin
(get_codegen ())
end))


let codegen_libs : Prims.unit  ->  Prims.string Prims.list Prims.list = (fun _24_392 -> (match (()) with
| () -> begin
(let _113_515 = (get_codegen_lib ())
in (FStar_All.pipe_right _113_515 (FStar_List.map (fun x -> (FStar_Util.split x ".")))))
end))


let debug_any : Prims.unit  ->  Prims.bool = (fun _24_394 -> (match (()) with
| () -> begin
((get_debug ()) <> [])
end))


let debug_at_level : Prims.string  ->  debug_level_t  ->  Prims.bool = (fun modul level -> ((let _113_522 = (get_debug ())
in (FStar_All.pipe_right _113_522 (FStar_List.contains modul))) && (debug_level_geq level)))


let dep : Prims.unit  ->  Prims.string Prims.option = (fun _24_397 -> (match (()) with
| () -> begin
(get_dep ())
end))


let detail_errors : Prims.unit  ->  Prims.bool = (fun _24_398 -> (match (()) with
| () -> begin
(get_detail_errors ())
end))


let dump_module : Prims.string  ->  Prims.bool = (fun s -> (let _113_529 = (get_dump_module ())
in (FStar_All.pipe_right _113_529 (FStar_List.contains s))))


let eager_inference : Prims.unit  ->  Prims.bool = (fun _24_400 -> (match (()) with
| () -> begin
(get_eager_inference ())
end))


let explicit_deps : Prims.unit  ->  Prims.bool = (fun _24_401 -> (match (()) with
| () -> begin
(get_explicit_deps ())
end))


let fs_typ_app : Prims.unit  ->  Prims.bool = (fun _24_402 -> (match (()) with
| () -> begin
(get_fs_typ_app ())
end))


let full_context_dependency : Prims.unit  ->  Prims.bool = (fun _24_403 -> (match (()) with
| () -> begin
((get_MLish ()) = false)
end))


let hide_genident_nums : Prims.unit  ->  Prims.bool = (fun _24_404 -> (match (()) with
| () -> begin
(get_hide_genident_nums ())
end))


let hide_uvar_nums : Prims.unit  ->  Prims.bool = (fun _24_405 -> (match (()) with
| () -> begin
(get_hide_uvar_nums ())
end))


let initial_fuel : Prims.unit  ->  Prims.int = (fun _24_406 -> (match (()) with
| () -> begin
(get_initial_fuel ())
end))


let initial_ifuel : Prims.unit  ->  Prims.int = (fun _24_407 -> (match (()) with
| () -> begin
(get_initial_ifuel ())
end))


let inline_arith : Prims.unit  ->  Prims.bool = (fun _24_408 -> (match (()) with
| () -> begin
(get_inline_arith ())
end))


let interactive : Prims.unit  ->  Prims.bool = (fun _24_409 -> (match (()) with
| () -> begin
(get_in ())
end))


let interactive_fsi : Prims.unit  ->  Prims.bool = (fun _24_410 -> (match (()) with
| () -> begin
(get_fsi ())
end))


let lax : Prims.unit  ->  Prims.bool = (fun _24_411 -> (match (()) with
| () -> begin
(get_lax ())
end))


let log_queries : Prims.unit  ->  Prims.bool = (fun _24_412 -> (match (()) with
| () -> begin
(get_log_queries ())
end))


let log_types : Prims.unit  ->  Prims.bool = (fun _24_413 -> (match (()) with
| () -> begin
(get_log_types ())
end))


let max_fuel : Prims.unit  ->  Prims.int = (fun _24_414 -> (match (()) with
| () -> begin
(get_max_fuel ())
end))


let max_ifuel : Prims.unit  ->  Prims.int = (fun _24_415 -> (match (()) with
| () -> begin
(get_max_ifuel ())
end))


let min_fuel : Prims.unit  ->  Prims.int = (fun _24_416 -> (match (()) with
| () -> begin
(get_min_fuel ())
end))


let ml_ish : Prims.unit  ->  Prims.bool = (fun _24_417 -> (match (()) with
| () -> begin
(get_MLish ())
end))


let n_cores : Prims.unit  ->  Prims.int = (fun _24_418 -> (match (()) with
| () -> begin
(get_n_cores ())
end))


let no_default_includes : Prims.unit  ->  Prims.bool = (fun _24_419 -> (match (()) with
| () -> begin
(get_no_default_includes ())
end))


let no_extract : Prims.string  ->  Prims.bool = (fun s -> (let _113_572 = (get_no_extract ())
in (FStar_All.pipe_right _113_572 (FStar_List.contains s))))


let no_location_info : Prims.unit  ->  Prims.bool = (fun _24_421 -> (match (()) with
| () -> begin
(get_no_location_info ())
end))


let norm_then_print : Prims.unit  ->  Prims.bool = (fun _24_422 -> (match (()) with
| () -> begin
((get_print_before_norm ()) = false)
end))


let output_dir : Prims.unit  ->  Prims.string Prims.option = (fun _24_423 -> (match (()) with
| () -> begin
(get_odir ())
end))


let print_bound_var_types : Prims.unit  ->  Prims.bool = (fun _24_424 -> (match (()) with
| () -> begin
(get_print_bound_var_types ())
end))


let print_effect_args : Prims.unit  ->  Prims.bool = (fun _24_425 -> (match (()) with
| () -> begin
(get_print_effect_args ())
end))


let print_fuels : Prims.unit  ->  Prims.bool = (fun _24_426 -> (match (()) with
| () -> begin
(get_print_fuels ())
end))


let print_implicits : Prims.unit  ->  Prims.bool = (fun _24_427 -> (match (()) with
| () -> begin
(get_print_implicits ())
end))


let print_real_names : Prims.unit  ->  Prims.bool = (fun _24_428 -> (match (()) with
| () -> begin
(get_prn ())
end))


let print_universes : Prims.unit  ->  Prims.bool = (fun _24_429 -> (match (()) with
| () -> begin
(get_print_universes ())
end))


let silent : Prims.unit  ->  Prims.bool = (fun _24_430 -> (match (()) with
| () -> begin
(get_silent ())
end))


let split_cases : Prims.unit  ->  Prims.int = (fun _24_431 -> (match (()) with
| () -> begin
(get_split_cases ())
end))


let timing : Prims.unit  ->  Prims.bool = (fun _24_432 -> (match (()) with
| () -> begin
(get_timing ())
end))


let trace_error : Prims.unit  ->  Prims.bool = (fun _24_433 -> (match (()) with
| () -> begin
(get_trace_error ())
end))


let universes : Prims.unit  ->  Prims.bool = (fun _24_434 -> (match (()) with
| () -> begin
(get_universes ())
end))


let unthrottle_inductives : Prims.unit  ->  Prims.bool = (fun _24_435 -> (match (()) with
| () -> begin
(get_unthrottle_inductives ())
end))


let use_eq_at_higher_order : Prims.unit  ->  Prims.bool = (fun _24_436 -> (match (()) with
| () -> begin
(get_use_eq_at_higher_order ())
end))


let use_native_int : Prims.unit  ->  Prims.bool = (fun _24_437 -> (match (()) with
| () -> begin
(get_use_native_int ())
end))


let verify_module : Prims.unit  ->  Prims.string Prims.list = (fun _24_438 -> (match (()) with
| () -> begin
(get_verify_module ())
end))


let warn_cardinality : Prims.unit  ->  Prims.bool = (fun _24_439 -> (match (()) with
| () -> begin
((get_cardinality ()) = "warn")
end))


let warn_top_level_effects : Prims.unit  ->  Prims.bool = (fun _24_440 -> (match (()) with
| () -> begin
(get_warn_top_level_effects ())
end))


let z3_exe : Prims.unit  ->  Prims.string = (fun _24_441 -> (match (()) with
| () -> begin
(match ((get_smt ())) with
| None -> begin
(FStar_Platform.exe "z3")
end
| Some (s) -> begin
s
end)
end))


let z3_timeout : Prims.unit  ->  Prims.int = (fun _24_445 -> (match (()) with
| () -> begin
(get_z3timeout ())
end))




