open Prims
type debug_level_t =
  | Low
  | Medium
  | High
  | Extreme
  | Other of Prims.string[@@deriving show]
let uu___is_Low: debug_level_t -> Prims.bool =
  fun projectee  -> match projectee with | Low  -> true | uu____8 -> false
let uu___is_Medium: debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____12 -> false
let uu___is_High: debug_level_t -> Prims.bool =
  fun projectee  -> match projectee with | High  -> true | uu____16 -> false
let uu___is_Extreme: debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____20 -> false
let uu___is_Other: debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____25 -> false
let __proj__Other__item___0: debug_level_t -> Prims.string =
  fun projectee  -> match projectee with | Other _0 -> _0
type option_val =
  | Bool of Prims.bool
  | String of Prims.string
  | Path of Prims.string
  | Int of Prims.int
  | List of option_val Prims.list
  | Unset[@@deriving show]
let uu___is_Bool: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____59 -> false
let __proj__Bool__item___0: option_val -> Prims.bool =
  fun projectee  -> match projectee with | Bool _0 -> _0
let uu___is_String: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____71 -> false
let __proj__String__item___0: option_val -> Prims.string =
  fun projectee  -> match projectee with | String _0 -> _0
let uu___is_Path: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____83 -> false
let __proj__Path__item___0: option_val -> Prims.string =
  fun projectee  -> match projectee with | Path _0 -> _0
let uu___is_Int: option_val -> Prims.bool =
  fun projectee  -> match projectee with | Int _0 -> true | uu____95 -> false
let __proj__Int__item___0: option_val -> Prims.int =
  fun projectee  -> match projectee with | Int _0 -> _0
let uu___is_List: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____109 -> false
let __proj__List__item___0: option_val -> option_val Prims.list =
  fun projectee  -> match projectee with | List _0 -> _0
let uu___is_Unset: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____126 -> false
let mk_bool: Prims.bool -> option_val = fun _0_27  -> Bool _0_27
let mk_string: Prims.string -> option_val = fun _0_28  -> String _0_28
let mk_path: Prims.string -> option_val = fun _0_29  -> Path _0_29
let mk_int: Prims.int -> option_val = fun _0_30  -> Int _0_30
let mk_list: option_val Prims.list -> option_val = fun _0_31  -> List _0_31
type options =
  | Set
  | Reset
  | Restore[@@deriving show]
let uu___is_Set: options -> Prims.bool =
  fun projectee  -> match projectee with | Set  -> true | uu____142 -> false
let uu___is_Reset: options -> Prims.bool =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____146 -> false
let uu___is_Restore: options -> Prims.bool =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____150 -> false
let __unit_tests__: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let __unit_tests: Prims.unit -> Prims.bool =
  fun uu____166  -> FStar_ST.op_Bang __unit_tests__
let __set_unit_tests: Prims.unit -> Prims.unit =
  fun uu____188  -> FStar_ST.op_Colon_Equals __unit_tests__ true
let __clear_unit_tests: Prims.unit -> Prims.unit =
  fun uu____210  -> FStar_ST.op_Colon_Equals __unit_tests__ false
let as_bool: option_val -> Prims.bool =
  fun uu___35_232  ->
    match uu___35_232 with
    | Bool b -> b
    | uu____234 -> failwith "Impos: expected Bool"
let as_int: option_val -> Prims.int =
  fun uu___36_237  ->
    match uu___36_237 with
    | Int b -> b
    | uu____239 -> failwith "Impos: expected Int"
let as_string: option_val -> Prims.string =
  fun uu___37_242  ->
    match uu___37_242 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____245 -> failwith "Impos: expected String"
let as_list': option_val -> option_val Prims.list =
  fun uu___38_250  ->
    match uu___38_250 with
    | List ts -> ts
    | uu____256 -> failwith "Impos: expected List"
let as_list:
  'Auu____262 .
    (option_val -> 'Auu____262) -> option_val -> 'Auu____262 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____278 = as_list' x in
      FStar_All.pipe_right uu____278 (FStar_List.map as_t)
let as_option:
  'Auu____288 .
    (option_val -> 'Auu____288) ->
      option_val -> 'Auu____288 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___39_301  ->
      match uu___39_301 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____305 = as_t v1 in FStar_Pervasives_Native.Some uu____305
type optionstate = option_val FStar_Util.smap[@@deriving show]
let fstar_options: optionstate Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let peek: Prims.unit -> optionstate =
  fun uu____327  ->
    let uu____328 = FStar_ST.op_Bang fstar_options in FStar_List.hd uu____328
let pop: Prims.unit -> Prims.unit =
  fun uu____356  ->
    let uu____357 = FStar_ST.op_Bang fstar_options in
    match uu____357 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____383::[] -> failwith "TOO MANY POPS!"
    | uu____384::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
let push: Prims.unit -> Prims.unit =
  fun uu____413  ->
    let uu____414 =
      let uu____417 =
        let uu____420 = peek () in FStar_Util.smap_copy uu____420 in
      let uu____423 = FStar_ST.op_Bang fstar_options in uu____417 ::
        uu____423 in
    FStar_ST.op_Colon_Equals fstar_options uu____414
let set: optionstate -> Prims.unit =
  fun o  ->
    let uu____479 = FStar_ST.op_Bang fstar_options in
    match uu____479 with
    | [] -> failwith "set on empty option stack"
    | uu____505::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
let set_option: Prims.string -> option_val -> Prims.unit =
  fun k  ->
    fun v1  -> let uu____538 = peek () in FStar_Util.smap_add uu____538 k v1
let set_option':
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> Prims.unit =
  fun uu____547  -> match uu____547 with | (k,v1) -> set_option k v1
let with_saved_options: 'a . (Prims.unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f () in pop (); retv)
let light_off_files: Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let add_light_off_file: Prims.string -> Prims.unit =
  fun filename  ->
    let uu____589 =
      let uu____592 = FStar_ST.op_Bang light_off_files in filename ::
        uu____592 in
    FStar_ST.op_Colon_Equals light_off_files uu____589
let defaults:
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 Prims.list =
  [("__temp_no_proj", (List []));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
  ("cache_checked_modules", (Bool false));
  ("cache_dir", Unset);
  ("codegen", Unset);
  ("codegen-lib", (List []));
  ("debug", (List []));
  ("debug_level", (List []));
  ("dep", Unset);
  ("detail_errors", (Bool false));
  ("detail_hint_replay", (Bool false));
  ("doc", (Bool false));
  ("dump_module", (List []));
  ("eager_inference", (Bool false));
  ("expose_interfaces", (Bool false));
  ("extract", Unset);
  ("extract_all", (Bool false));
  ("extract_module", (List []));
  ("extract_namespace", (List []));
  ("fs_typ_app", (Bool false));
  ("fstar_home", Unset);
  ("full_context_dependency", (Bool true));
  ("gen_native_tactics", Unset);
  ("hide_uvar_nums", (Bool false));
  ("hint_info", (Bool false));
  ("hint_file", Unset);
  ("in", (Bool false));
  ("ide", (Bool false));
  ("include", (List []));
  ("indent", (Bool false));
  ("initial_fuel", (Int (Prims.parse_int "2")));
  ("initial_ifuel", (Int (Prims.parse_int "1")));
  ("lax", (Bool false));
  ("load", (List []));
  ("log_queries", (Bool false));
  ("log_types", (Bool false));
  ("max_fuel", (Int (Prims.parse_int "8")));
  ("max_ifuel", (Int (Prims.parse_int "2")));
  ("min_fuel", (Int (Prims.parse_int "1")));
  ("MLish", (Bool false));
  ("n_cores", (Int (Prims.parse_int "1")));
  ("no_default_includes", (Bool false));
  ("no_extract", (List []));
  ("no_location_info", (Bool false));
  ("no_tactics", (Bool false));
  ("normalize_pure_terms_for_extraction", (Bool false));
  ("odir", Unset);
  ("prims", Unset);
  ("pretype", (Bool true));
  ("prims_ref", Unset);
  ("print_bound_var_types", (Bool false));
  ("print_effect_args", (Bool false));
  ("print_full_names", (Bool false));
  ("print_implicits", (Bool false));
  ("print_universes", (Bool false));
  ("print_z3_statistics", (Bool false));
  ("prn", (Bool false));
  ("query_stats", (Bool false));
  ("record_hints", (Bool false));
  ("reuse_hint_for", Unset);
  ("silent", (Bool false));
  ("smt", Unset);
  ("smtencoding.elim_box", (Bool false));
  ("smtencoding.nl_arith_repr", (String "boxwrap"));
  ("smtencoding.l_arith_repr", (String "boxwrap"));
  ("tactic_raw_binders", (Bool false));
  ("tactic_trace", (Bool false));
  ("tactic_trace_d", (Int (Prims.parse_int "0")));
  ("timing", (Bool false));
  ("trace_error", (Bool false));
  ("ugly", (Bool false));
  ("unthrottle_inductives", (Bool false));
  ("unsafe_tactic_exec", (Bool false));
  ("use_native_tactics", Unset);
  ("use_eq_at_higher_order", (Bool false));
  ("use_hints", (Bool false));
  ("use_hint_hashes", (Bool false));
  ("using_facts_from", Unset);
  ("vcgen.optimize_bind_as_seq", Unset);
  ("verify_module", (List []));
  ("warn_default_effects", (Bool false));
  ("z3refresh", (Bool false));
  ("z3rlimit", (Int (Prims.parse_int "5")));
  ("z3rlimit_factor", (Int (Prims.parse_int "1")));
  ("z3seed", (Int (Prims.parse_int "0")));
  ("z3cliopt", (List []));
  ("use_two_phase_tc", (Bool false));
  ("__no_positivity", (Bool false));
  ("__ml_no_eta_expand_coertions", (Bool false));
  ("warn_error", (String ""))]
let init: Prims.unit -> Prims.unit =
  fun uu____1017  ->
    let o = peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let clear: Prims.unit -> Prims.unit =
  fun uu____1032  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50") in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
let _run: Prims.unit = clear ()
let get_option: Prims.string -> option_val =
  fun s  ->
    let uu____1091 =
      let uu____1094 = peek () in FStar_Util.smap_try_find uu____1094 s in
    match uu____1091 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
let lookup_opt:
  'Auu____1101 . Prims.string -> (option_val -> 'Auu____1101) -> 'Auu____1101
  = fun s  -> fun c  -> c (get_option s)
let get_admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____1117  -> lookup_opt "admit_smt_queries" as_bool
let get_admit_except:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1122  -> lookup_opt "admit_except" (as_option as_string)
let get_cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____1127  -> lookup_opt "cache_checked_modules" as_bool
let get_cache_dir: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1132  -> lookup_opt "cache_dir" (as_option as_string)
let get_codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1139  -> lookup_opt "codegen" (as_option as_string)
let get_codegen_lib: Prims.unit -> Prims.string Prims.list =
  fun uu____1146  -> lookup_opt "codegen-lib" (as_list as_string)
let get_debug: Prims.unit -> Prims.string Prims.list =
  fun uu____1153  -> lookup_opt "debug" (as_list as_string)
let get_debug_level: Prims.unit -> Prims.string Prims.list =
  fun uu____1160  -> lookup_opt "debug_level" (as_list as_string)
let get_dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1167  -> lookup_opt "dep" (as_option as_string)
let get_detail_errors: Prims.unit -> Prims.bool =
  fun uu____1172  -> lookup_opt "detail_errors" as_bool
let get_detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____1175  -> lookup_opt "detail_hint_replay" as_bool
let get_doc: Prims.unit -> Prims.bool =
  fun uu____1178  -> lookup_opt "doc" as_bool
let get_dump_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1183  -> lookup_opt "dump_module" (as_list as_string)
let get_eager_inference: Prims.unit -> Prims.bool =
  fun uu____1188  -> lookup_opt "eager_inference" as_bool
let get_expose_interfaces: Prims.unit -> Prims.bool =
  fun uu____1191  -> lookup_opt "expose_interfaces" as_bool
let get_extract:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1198  -> lookup_opt "extract" (as_option (as_list as_string))
let get_extract_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1209  -> lookup_opt "extract_module" (as_list as_string)
let get_extract_namespace: Prims.unit -> Prims.string Prims.list =
  fun uu____1216  -> lookup_opt "extract_namespace" (as_list as_string)
let get_fs_typ_app: Prims.unit -> Prims.bool =
  fun uu____1221  -> lookup_opt "fs_typ_app" as_bool
let get_fstar_home: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1226  -> lookup_opt "fstar_home" (as_option as_string)
let get_gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1233  -> lookup_opt "gen_native_tactics" (as_option as_string)
let get_hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____1238  -> lookup_opt "hide_uvar_nums" as_bool
let get_hint_info: Prims.unit -> Prims.bool =
  fun uu____1241  -> lookup_opt "hint_info" as_bool
let get_hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1246  -> lookup_opt "hint_file" (as_option as_string)
let get_in: Prims.unit -> Prims.bool =
  fun uu____1251  -> lookup_opt "in" as_bool
let get_ide: Prims.unit -> Prims.bool =
  fun uu____1254  -> lookup_opt "ide" as_bool
let get_include: Prims.unit -> Prims.string Prims.list =
  fun uu____1259  -> lookup_opt "include" (as_list as_string)
let get_indent: Prims.unit -> Prims.bool =
  fun uu____1264  -> lookup_opt "indent" as_bool
let get_initial_fuel: Prims.unit -> Prims.int =
  fun uu____1267  -> lookup_opt "initial_fuel" as_int
let get_initial_ifuel: Prims.unit -> Prims.int =
  fun uu____1270  -> lookup_opt "initial_ifuel" as_int
let get_lax: Prims.unit -> Prims.bool =
  fun uu____1273  -> lookup_opt "lax" as_bool
let get_load: Prims.unit -> Prims.string Prims.list =
  fun uu____1278  -> lookup_opt "load" (as_list as_string)
let get_log_queries: Prims.unit -> Prims.bool =
  fun uu____1283  -> lookup_opt "log_queries" as_bool
let get_log_types: Prims.unit -> Prims.bool =
  fun uu____1286  -> lookup_opt "log_types" as_bool
let get_max_fuel: Prims.unit -> Prims.int =
  fun uu____1289  -> lookup_opt "max_fuel" as_int
let get_max_ifuel: Prims.unit -> Prims.int =
  fun uu____1292  -> lookup_opt "max_ifuel" as_int
let get_min_fuel: Prims.unit -> Prims.int =
  fun uu____1295  -> lookup_opt "min_fuel" as_int
let get_MLish: Prims.unit -> Prims.bool =
  fun uu____1298  -> lookup_opt "MLish" as_bool
let get_n_cores: Prims.unit -> Prims.int =
  fun uu____1301  -> lookup_opt "n_cores" as_int
let get_no_default_includes: Prims.unit -> Prims.bool =
  fun uu____1304  -> lookup_opt "no_default_includes" as_bool
let get_no_extract: Prims.unit -> Prims.string Prims.list =
  fun uu____1309  -> lookup_opt "no_extract" (as_list as_string)
let get_no_location_info: Prims.unit -> Prims.bool =
  fun uu____1314  -> lookup_opt "no_location_info" as_bool
let get_normalize_pure_terms_for_extraction: Prims.unit -> Prims.bool =
  fun uu____1317  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool
let get_odir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1322  -> lookup_opt "odir" (as_option as_string)
let get_ugly: Prims.unit -> Prims.bool =
  fun uu____1327  -> lookup_opt "ugly" as_bool
let get_prims: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1332  -> lookup_opt "prims" (as_option as_string)
let get_print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____1337  -> lookup_opt "print_bound_var_types" as_bool
let get_print_effect_args: Prims.unit -> Prims.bool =
  fun uu____1340  -> lookup_opt "print_effect_args" as_bool
let get_print_full_names: Prims.unit -> Prims.bool =
  fun uu____1343  -> lookup_opt "print_full_names" as_bool
let get_print_implicits: Prims.unit -> Prims.bool =
  fun uu____1346  -> lookup_opt "print_implicits" as_bool
let get_print_universes: Prims.unit -> Prims.bool =
  fun uu____1349  -> lookup_opt "print_universes" as_bool
let get_print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____1352  -> lookup_opt "print_z3_statistics" as_bool
let get_prn: Prims.unit -> Prims.bool =
  fun uu____1355  -> lookup_opt "prn" as_bool
let get_query_stats: Prims.unit -> Prims.bool =
  fun uu____1358  -> lookup_opt "query_stats" as_bool
let get_record_hints: Prims.unit -> Prims.bool =
  fun uu____1361  -> lookup_opt "record_hints" as_bool
let get_reuse_hint_for:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1366  -> lookup_opt "reuse_hint_for" (as_option as_string)
let get_silent: Prims.unit -> Prims.bool =
  fun uu____1371  -> lookup_opt "silent" as_bool
let get_smt: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1376  -> lookup_opt "smt" (as_option as_string)
let get_smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____1381  -> lookup_opt "smtencoding.elim_box" as_bool
let get_smtencoding_nl_arith_repr: Prims.unit -> Prims.string =
  fun uu____1384  -> lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr: Prims.unit -> Prims.string =
  fun uu____1387  -> lookup_opt "smtencoding.l_arith_repr" as_string
let get_tactic_raw_binders: Prims.unit -> Prims.bool =
  fun uu____1390  -> lookup_opt "tactic_raw_binders" as_bool
let get_tactic_trace: Prims.unit -> Prims.bool =
  fun uu____1393  -> lookup_opt "tactic_trace" as_bool
let get_tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____1396  -> lookup_opt "tactic_trace_d" as_int
let get_timing: Prims.unit -> Prims.bool =
  fun uu____1399  -> lookup_opt "timing" as_bool
let get_trace_error: Prims.unit -> Prims.bool =
  fun uu____1402  -> lookup_opt "trace_error" as_bool
let get_unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____1405  -> lookup_opt "unthrottle_inductives" as_bool
let get_unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____1408  -> lookup_opt "unsafe_tactic_exec" as_bool
let get_use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____1411  -> lookup_opt "use_eq_at_higher_order" as_bool
let get_use_hints: Prims.unit -> Prims.bool =
  fun uu____1414  -> lookup_opt "use_hints" as_bool
let get_use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____1417  -> lookup_opt "use_hint_hashes" as_bool
let get_use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1422  -> lookup_opt "use_native_tactics" (as_option as_string)
let get_use_tactics: Prims.unit -> Prims.bool =
  fun uu____1427  ->
    let uu____1428 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____1428
let get_using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1435  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let get_vcgen_optimize_bind_as_seq:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1446  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
let get_verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1453  -> lookup_opt "verify_module" (as_list as_string)
let get___temp_no_proj: Prims.unit -> Prims.string Prims.list =
  fun uu____1460  -> lookup_opt "__temp_no_proj" (as_list as_string)
let get_version: Prims.unit -> Prims.bool =
  fun uu____1465  -> lookup_opt "version" as_bool
let get_warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____1468  -> lookup_opt "warn_default_effects" as_bool
let get_z3cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____1473  -> lookup_opt "z3cliopt" (as_list as_string)
let get_z3refresh: Prims.unit -> Prims.bool =
  fun uu____1478  -> lookup_opt "z3refresh" as_bool
let get_z3rlimit: Prims.unit -> Prims.int =
  fun uu____1481  -> lookup_opt "z3rlimit" as_int
let get_z3rlimit_factor: Prims.unit -> Prims.int =
  fun uu____1484  -> lookup_opt "z3rlimit_factor" as_int
let get_z3seed: Prims.unit -> Prims.int =
  fun uu____1487  -> lookup_opt "z3seed" as_int
let get_use_two_phase_tc: Prims.unit -> Prims.bool =
  fun uu____1490  -> lookup_opt "use_two_phase_tc" as_bool
let get_no_positivity: Prims.unit -> Prims.bool =
  fun uu____1493  -> lookup_opt "__no_positivity" as_bool
let get_ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____1496  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool
let get_warn_error: Prims.unit -> Prims.string =
  fun uu____1499  -> lookup_opt "warn_error" as_string
let dlevel: Prims.string -> debug_level_t =
  fun uu___40_1502  ->
    match uu___40_1502 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let one_debug_level_geq: debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1510 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let debug_level_geq: debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____1514 = get_debug_level () in
    FStar_All.pipe_right uu____1514
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
let universe_include_path_base_dirs: Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"]
let _version: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _platform: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _compiler: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _date: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _commit: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let display_version: Prims.unit -> Prims.unit =
  fun uu____1645  ->
    let uu____1646 =
      let uu____1647 = FStar_ST.op_Bang _version in
      let uu____1667 = FStar_ST.op_Bang _platform in
      let uu____1687 = FStar_ST.op_Bang _compiler in
      let uu____1707 = FStar_ST.op_Bang _date in
      let uu____1727 = FStar_ST.op_Bang _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1647
        uu____1667 uu____1687 uu____1707 uu____1727 in
    FStar_Util.print_string uu____1646
let display_usage_aux:
  'Auu____1750 'Auu____1751 .
    ('Auu____1751,Prims.string,'Auu____1750 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____1798  ->
         match uu____1798 with
         | (uu____1809,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____1820 =
                      let uu____1821 = FStar_Util.colorize_bold flag in
                      FStar_Util.format1 "  --%s\n" uu____1821 in
                    FStar_Util.print_string uu____1820
                  else
                    (let uu____1823 =
                       let uu____1824 = FStar_Util.colorize_bold flag in
                       FStar_Util.format2 "  --%s  %s\n" uu____1824 doc in
                     FStar_Util.print_string uu____1823)
              | FStar_Getopt.OneArg (uu____1825,argname) ->
                  if doc = ""
                  then
                    let uu____1831 =
                      let uu____1832 = FStar_Util.colorize_bold flag in
                      let uu____1833 = FStar_Util.colorize_bold argname in
                      FStar_Util.format2 "  --%s %s\n" uu____1832 uu____1833 in
                    FStar_Util.print_string uu____1831
                  else
                    (let uu____1835 =
                       let uu____1836 = FStar_Util.colorize_bold flag in
                       let uu____1837 = FStar_Util.colorize_bold argname in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____1836
                         uu____1837 doc in
                     FStar_Util.print_string uu____1835))) specs
let mk_spec:
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____1861 = o in
    match uu____1861 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____1891 =
                let uu____1892 = f () in set_option name uu____1892 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____1903 = f x in set_option name uu____1903 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____1917 = lookup_opt name (as_option as_list') in
        FStar_Util.dflt [] uu____1917 in
      mk_list (value :: prev_values)
let reverse_accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let uu____1936 =
        let uu____1939 = lookup_opt name as_list' in
        FStar_List.append uu____1939 [value] in
      mk_list uu____1936
let accumulate_string:
  'Auu____1948 .
    Prims.string ->
      ('Auu____1948 -> Prims.string) -> 'Auu____1948 -> Prims.unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____1966 =
          let uu____1967 =
            let uu____1968 = post_processor value in mk_string uu____1968 in
          accumulated_option name uu____1967 in
        set_option name uu____1966
let add_extract_module: Prims.string -> Prims.unit =
  fun s  -> accumulate_string "extract_module" FStar_String.lowercase s
let add_extract_namespace: Prims.string -> Prims.unit =
  fun s  -> accumulate_string "extract_namespace" FStar_String.lowercase s
let add_verify_module: Prims.string -> Prims.unit =
  fun s  -> accumulate_string "verify_module" FStar_String.lowercase s
type opt_type =
  | Const of option_val
  | IntStr of Prims.string
  | BoolStr
  | PathStr of Prims.string
  | SimpleStr of Prims.string
  | EnumStr of Prims.string Prims.list
  | OpenEnumStr of (Prims.string Prims.list,Prims.string)
  FStar_Pervasives_Native.tuple2
  | PostProcessed of (option_val -> option_val,opt_type)
  FStar_Pervasives_Native.tuple2
  | Accumulated of opt_type
  | ReverseAccumulated of opt_type
  | WithSideEffect of (Prims.unit -> Prims.unit,opt_type)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Const: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____2046 -> false
let __proj__Const__item___0: opt_type -> option_val =
  fun projectee  -> match projectee with | Const _0 -> _0
let uu___is_IntStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2058 -> false
let __proj__IntStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | IntStr _0 -> _0
let uu___is_BoolStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2069 -> false
let uu___is_PathStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2074 -> false
let __proj__PathStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | PathStr _0 -> _0
let uu___is_SimpleStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2086 -> false
let __proj__SimpleStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0
let uu___is_EnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2100 -> false
let __proj__EnumStr__item___0: opt_type -> Prims.string Prims.list =
  fun projectee  -> match projectee with | EnumStr _0 -> _0
let uu___is_OpenEnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2124 -> false
let __proj__OpenEnumStr__item___0:
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0
let uu___is_PostProcessed: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2160 -> false
let __proj__PostProcessed__item___0:
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0
let uu___is_Accumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2190 -> false
let __proj__Accumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | Accumulated _0 -> _0
let uu___is_ReverseAccumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2202 -> false
let __proj__ReverseAccumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0
let uu___is_WithSideEffect: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2220 -> false
let __proj__WithSideEffect__item___0:
  opt_type ->
    (Prims.unit -> Prims.unit,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | WithSideEffect _0 -> _0
exception InvalidArgument of Prims.string
let uu___is_InvalidArgument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2252 -> true
    | uu____2253 -> false
let __proj__InvalidArgument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2260 -> uu____2260
let rec parse_opt_val: Prims.string -> opt_type -> Prims.string -> option_val
  =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2274 ->
              let uu____2275 = FStar_Util.safe_int_of_string str_val in
              (match uu____2275 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2279 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name) in
              mk_bool uu____2279
          | PathStr uu____2282 -> mk_path str_val
          | SimpleStr uu____2283 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2288 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2301 = parse_opt_val opt_name elem_spec str_val in
              pp uu____2301
          | Accumulated elem_spec ->
              let v1 = parse_opt_val opt_name elem_spec str_val in
              accumulated_option opt_name v1
          | ReverseAccumulated elem_spec ->
              let v1 = parse_opt_val opt_name elem_spec str_val in
              reverse_accumulated_option opt_name v1
          | WithSideEffect (side_effect,elem_spec) ->
              (side_effect (); parse_opt_val opt_name elem_spec str_val)
        with
        | InvalidArgument opt_name1 ->
            let uu____2318 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1 in
            failwith uu____2318
let rec desc_of_opt_type:
  opt_type -> Prims.string FStar_Pervasives_Native.option =
  fun typ  ->
    let desc_of_enum cases =
      FStar_Pervasives_Native.Some
        (Prims.strcat "[" (Prims.strcat (FStar_String.concat "|" cases) "]")) in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____2351,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2359,elem_spec) -> desc_of_opt_type elem_spec
let rec arg_spec_of_opt_type:
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ in
      let uu____2378 = desc_of_opt_type typ in
      match uu____2378 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2384  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
let pp_validate_dir: option_val -> option_val =
  fun p  -> let pp = as_string p in FStar_Util.mkdir false pp; p
let pp_lowercase: option_val -> option_val =
  fun s  ->
    let uu____2396 =
      let uu____2397 = as_string s in FStar_String.lowercase uu____2397 in
    mk_string uu____2396
let rec specs_with_types:
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun uu____2414  ->
    let uu____2425 =
      let uu____2436 =
        let uu____2447 =
          let uu____2456 = let uu____2457 = mk_bool true in Const uu____2457 in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2456,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying") in
        let uu____2458 =
          let uu____2469 =
            let uu____2480 =
              let uu____2491 =
                let uu____2502 =
                  let uu____2513 =
                    let uu____2524 =
                      let uu____2535 =
                        let uu____2544 =
                          let uu____2545 = mk_bool true in Const uu____2545 in
                        (FStar_Getopt.noshort, "detail_errors", uu____2544,
                          "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1") in
                      let uu____2546 =
                        let uu____2557 =
                          let uu____2566 =
                            let uu____2567 = mk_bool true in Const uu____2567 in
                          (FStar_Getopt.noshort, "detail_hint_replay",
                            uu____2566,
                            "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1") in
                        let uu____2568 =
                          let uu____2579 =
                            let uu____2588 =
                              let uu____2589 = mk_bool true in
                              Const uu____2589 in
                            (FStar_Getopt.noshort, "doc", uu____2588,
                              "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.") in
                          let uu____2590 =
                            let uu____2601 =
                              let uu____2612 =
                                let uu____2621 =
                                  let uu____2622 = mk_bool true in
                                  Const uu____2622 in
                                (FStar_Getopt.noshort, "eager_inference",
                                  uu____2621,
                                  "Solve all type-inference constraints eagerly; more efficient but at the cost of generality") in
                              let uu____2623 =
                                let uu____2634 =
                                  let uu____2645 =
                                    let uu____2656 =
                                      let uu____2667 =
                                        let uu____2676 =
                                          let uu____2677 = mk_bool true in
                                          Const uu____2677 in
                                        (FStar_Getopt.noshort,
                                          "expose_interfaces", uu____2676,
                                          "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)") in
                                      let uu____2678 =
                                        let uu____2689 =
                                          let uu____2700 =
                                            let uu____2711 =
                                              let uu____2720 =
                                                let uu____2721 = mk_bool true in
                                                Const uu____2721 in
                                              (FStar_Getopt.noshort,
                                                "hide_uvar_nums", uu____2720,
                                                "Don't print unification variable numbers") in
                                            let uu____2722 =
                                              let uu____2733 =
                                                let uu____2744 =
                                                  let uu____2753 =
                                                    let uu____2754 =
                                                      mk_bool true in
                                                    Const uu____2754 in
                                                  (FStar_Getopt.noshort,
                                                    "hint_info", uu____2753,
                                                    "Print information regarding hints (deprecated; use --query_stats instead)") in
                                                let uu____2755 =
                                                  let uu____2766 =
                                                    let uu____2775 =
                                                      let uu____2776 =
                                                        mk_bool true in
                                                      Const uu____2776 in
                                                    (FStar_Getopt.noshort,
                                                      "in", uu____2775,
                                                      "Legacy interactive mode; reads input from stdin") in
                                                  let uu____2777 =
                                                    let uu____2788 =
                                                      let uu____2797 =
                                                        let uu____2798 =
                                                          mk_bool true in
                                                        Const uu____2798 in
                                                      (FStar_Getopt.noshort,
                                                        "ide", uu____2797,
                                                        "JSON-based interactive mode for IDEs") in
                                                    let uu____2799 =
                                                      let uu____2810 =
                                                        let uu____2821 =
                                                          let uu____2830 =
                                                            let uu____2831 =
                                                              mk_bool true in
                                                            Const uu____2831 in
                                                          (FStar_Getopt.noshort,
                                                            "indent",
                                                            uu____2830,
                                                            "Parses and outputs the files on the command line") in
                                                        let uu____2832 =
                                                          let uu____2843 =
                                                            let uu____2854 =
                                                              let uu____2865
                                                                =
                                                                let uu____2874
                                                                  =
                                                                  let uu____2875
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                  Const
                                                                    uu____2875 in
                                                                (FStar_Getopt.noshort,
                                                                  "lax",
                                                                  uu____2874,
                                                                  "Run the lax-type checker only (admit all verification conditions)") in
                                                              let uu____2876
                                                                =
                                                                let uu____2887
                                                                  =
                                                                  let uu____2898
                                                                    =
                                                                    let uu____2907
                                                                    =
                                                                    let uu____2908
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2908 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____2907,
                                                                    "Print types computed for data/val/let-bindings") in
                                                                  let uu____2909
                                                                    =
                                                                    let uu____2920
                                                                    =
                                                                    let uu____2929
                                                                    =
                                                                    let uu____2930
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2930 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____2929,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go") in
                                                                    let uu____2931
                                                                    =
                                                                    let uu____2942
                                                                    =
                                                                    let uu____2953
                                                                    =
                                                                    let uu____2964
                                                                    =
                                                                    let uu____2975
                                                                    =
                                                                    let uu____2984
                                                                    =
                                                                    let uu____2985
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2985 in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____2984,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)") in
                                                                    let uu____2986
                                                                    =
                                                                    let uu____2997
                                                                    =
                                                                    let uu____3008
                                                                    =
                                                                    let uu____3017
                                                                    =
                                                                    let uu____3018
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3018 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3017,
                                                                    "Ignore the default module search paths") in
                                                                    let uu____3019
                                                                    =
                                                                    let uu____3030
                                                                    =
                                                                    let uu____3041
                                                                    =
                                                                    let uu____3050
                                                                    =
                                                                    let uu____3051
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3051 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3050,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)") in
                                                                    let uu____3052
                                                                    =
                                                                    let uu____3063
                                                                    =
                                                                    let uu____3072
                                                                    =
                                                                    let uu____3073
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3073 in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3072,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.") in
                                                                    let uu____3074
                                                                    =
                                                                    let uu____3085
                                                                    =
                                                                    let uu____3096
                                                                    =
                                                                    let uu____3107
                                                                    =
                                                                    let uu____3116
                                                                    =
                                                                    let uu____3117
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3117 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3116,
                                                                    "Print the types of bound variables") in
                                                                    let uu____3118
                                                                    =
                                                                    let uu____3129
                                                                    =
                                                                    let uu____3138
                                                                    =
                                                                    let uu____3139
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3139 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3138,
                                                                    "Print inferred predicate transformers for all computation types") in
                                                                    let uu____3140
                                                                    =
                                                                    let uu____3151
                                                                    =
                                                                    let uu____3160
                                                                    =
                                                                    let uu____3161
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3161 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3160,
                                                                    "Print full names of variables") in
                                                                    let uu____3162
                                                                    =
                                                                    let uu____3173
                                                                    =
                                                                    let uu____3182
                                                                    =
                                                                    let uu____3183
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3183 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3182,
                                                                    "Print implicit arguments") in
                                                                    let uu____3184
                                                                    =
                                                                    let uu____3195
                                                                    =
                                                                    let uu____3204
                                                                    =
                                                                    let uu____3205
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3205 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3204,
                                                                    "Print universes") in
                                                                    let uu____3206
                                                                    =
                                                                    let uu____3217
                                                                    =
                                                                    let uu____3226
                                                                    =
                                                                    let uu____3227
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3227 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3226,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)") in
                                                                    let uu____3228
                                                                    =
                                                                    let uu____3239
                                                                    =
                                                                    let uu____3248
                                                                    =
                                                                    let uu____3249
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3249 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3248,
                                                                    "Print full names (deprecated; use --print_full_names instead)") in
                                                                    let uu____3250
                                                                    =
                                                                    let uu____3261
                                                                    =
                                                                    let uu____3270
                                                                    =
                                                                    let uu____3271
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3271 in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3270,
                                                                    "Print SMT query statistics") in
                                                                    let uu____3272
                                                                    =
                                                                    let uu____3283
                                                                    =
                                                                    let uu____3292
                                                                    =
                                                                    let uu____3293
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3293 in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3292,
                                                                    "Record a database of hints for efficient proof replay") in
                                                                    let uu____3294
                                                                    =
                                                                    let uu____3305
                                                                    =
                                                                    let uu____3316
                                                                    =
                                                                    let uu____3325
                                                                    =
                                                                    let uu____3326
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3326 in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3325,
                                                                    " ") in
                                                                    let uu____3327
                                                                    =
                                                                    let uu____3338
                                                                    =
                                                                    let uu____3349
                                                                    =
                                                                    let uu____3360
                                                                    =
                                                                    let uu____3371
                                                                    =
                                                                    let uu____3382
                                                                    =
                                                                    let uu____3391
                                                                    =
                                                                    let uu____3392
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3392 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____3391,
                                                                    "Do not use the lexical scope of tactics to improve binder names") in
                                                                    let uu____3393
                                                                    =
                                                                    let uu____3404
                                                                    =
                                                                    let uu____3413
                                                                    =
                                                                    let uu____3414
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3414 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3413,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)") in
                                                                    let uu____3415
                                                                    =
                                                                    let uu____3426
                                                                    =
                                                                    let uu____3437
                                                                    =
                                                                    let uu____3446
                                                                    =
                                                                    let uu____3447
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3447 in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3446,
                                                                    "Print the time it takes to verify each top-level definition") in
                                                                    let uu____3448
                                                                    =
                                                                    let uu____3459
                                                                    =
                                                                    let uu____3468
                                                                    =
                                                                    let uu____3469
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3469 in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3468,
                                                                    "Don't print an error message; show an exception trace instead") in
                                                                    let uu____3470
                                                                    =
                                                                    let uu____3481
                                                                    =
                                                                    let uu____3490
                                                                    =
                                                                    let uu____3491
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3491 in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3490,
                                                                    "Emit output formatted for debugging") in
                                                                    let uu____3492
                                                                    =
                                                                    let uu____3503
                                                                    =
                                                                    let uu____3512
                                                                    =
                                                                    let uu____3513
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3513 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____3512,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)") in
                                                                    let uu____3514
                                                                    =
                                                                    let uu____3525
                                                                    =
                                                                    let uu____3534
                                                                    =
                                                                    let uu____3535
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3535 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____3534,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.") in
                                                                    let uu____3536
                                                                    =
                                                                    let uu____3547
                                                                    =
                                                                    let uu____3556
                                                                    =
                                                                    let uu____3557
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3557 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____3556,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)") in
                                                                    let uu____3558
                                                                    =
                                                                    let uu____3569
                                                                    =
                                                                    let uu____3578
                                                                    =
                                                                    let uu____3579
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3579 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____3578,
                                                                    "Use a previously recorded hints database for proof replay") in
                                                                    let uu____3580
                                                                    =
                                                                    let uu____3591
                                                                    =
                                                                    let uu____3600
                                                                    =
                                                                    let uu____3601
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3601 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____3600,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database") in
                                                                    let uu____3602
                                                                    =
                                                                    let uu____3613
                                                                    =
                                                                    let uu____3624
                                                                    =
                                                                    let uu____3633
                                                                    =
                                                                    let uu____3634
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3634 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____3633,
                                                                    "Do not run the tactic engine before discharging a VC") in
                                                                    let uu____3635
                                                                    =
                                                                    let uu____3646
                                                                    =
                                                                    let uu____3657
                                                                    =
                                                                    let uu____3668
                                                                    =
                                                                    let uu____3679
                                                                    =
                                                                    let uu____3689
                                                                    =
                                                                    let uu____3690
                                                                    =
                                                                    let uu____3697
                                                                    =
                                                                    let uu____3698
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3698 in
                                                                    ((fun
                                                                    uu____3703
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____3697) in
                                                                    WithSideEffect
                                                                    uu____3690 in
                                                                    (118,
                                                                    "version",
                                                                    uu____3689,
                                                                    "Display version number") in
                                                                    let uu____3707
                                                                    =
                                                                    let uu____3719
                                                                    =
                                                                    let uu____3728
                                                                    =
                                                                    let uu____3729
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3729 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____3728,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)") in
                                                                    let uu____3730
                                                                    =
                                                                    let uu____3741
                                                                    =
                                                                    let uu____3752
                                                                    =
                                                                    let uu____3761
                                                                    =
                                                                    let uu____3762
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3762 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____3761,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness") in
                                                                    let uu____3763
                                                                    =
                                                                    let uu____3774
                                                                    =
                                                                    let uu____3785
                                                                    =
                                                                    let uu____3796
                                                                    =
                                                                    let uu____3807
                                                                    =
                                                                    let uu____3818
                                                                    =
                                                                    let uu____3827
                                                                    =
                                                                    let uu____3828
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3828 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____3827,
                                                                    "Don't check positivity of inductive types") in
                                                                    let uu____3829
                                                                    =
                                                                    let uu____3840
                                                                    =
                                                                    let uu____3849
                                                                    =
                                                                    let uu____3850
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3850 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____3849,
                                                                    "Do not eta-expand coertions in generated OCaml") in
                                                                    let uu____3851
                                                                    =
                                                                    let uu____3862
                                                                    =
                                                                    let uu____3873
                                                                    =
                                                                    let uu____3883
                                                                    =
                                                                    let uu____3884
                                                                    =
                                                                    let uu____3891
                                                                    =
                                                                    let uu____3892
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3892 in
                                                                    ((fun
                                                                    uu____3897
                                                                     ->
                                                                    (
                                                                    let uu____3899
                                                                    =
                                                                    specs () in
                                                                    display_usage_aux
                                                                    uu____3899);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____3891) in
                                                                    WithSideEffect
                                                                    uu____3884 in
                                                                    (104,
                                                                    "help",
                                                                    uu____3883,
                                                                    "Display this information") in
                                                                    [uu____3873] in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____3862 in
                                                                    uu____3840
                                                                    ::
                                                                    uu____3851 in
                                                                    uu____3818
                                                                    ::
                                                                    uu____3829 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'false')")
                                                                    ::
                                                                    uu____3807 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____3796 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____3785 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____3774 in
                                                                    uu____3752
                                                                    ::
                                                                    uu____3763 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____3741 in
                                                                    uu____3719
                                                                    ::
                                                                    uu____3730 in
                                                                    uu____3679
                                                                    ::
                                                                    uu____3707 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____3668 in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____3657 in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____3646 in
                                                                    uu____3624
                                                                    ::
                                                                    uu____3635 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____3613 in
                                                                    uu____3591
                                                                    ::
                                                                    uu____3602 in
                                                                    uu____3569
                                                                    ::
                                                                    uu____3580 in
                                                                    uu____3547
                                                                    ::
                                                                    uu____3558 in
                                                                    uu____3525
                                                                    ::
                                                                    uu____3536 in
                                                                    uu____3503
                                                                    ::
                                                                    uu____3514 in
                                                                    uu____3481
                                                                    ::
                                                                    uu____3492 in
                                                                    uu____3459
                                                                    ::
                                                                    uu____3470 in
                                                                    uu____3437
                                                                    ::
                                                                    uu____3448 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3426 in
                                                                    uu____3404
                                                                    ::
                                                                    uu____3415 in
                                                                    uu____3382
                                                                    ::
                                                                    uu____3393 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3371 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3360 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3349 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3338 in
                                                                    uu____3316
                                                                    ::
                                                                    uu____3327 in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3305 in
                                                                    uu____3283
                                                                    ::
                                                                    uu____3294 in
                                                                    uu____3261
                                                                    ::
                                                                    uu____3272 in
                                                                    uu____3239
                                                                    ::
                                                                    uu____3250 in
                                                                    uu____3217
                                                                    ::
                                                                    uu____3228 in
                                                                    uu____3195
                                                                    ::
                                                                    uu____3206 in
                                                                    uu____3173
                                                                    ::
                                                                    uu____3184 in
                                                                    uu____3151
                                                                    ::
                                                                    uu____3162 in
                                                                    uu____3129
                                                                    ::
                                                                    uu____3140 in
                                                                    uu____3107
                                                                    ::
                                                                    uu____3118 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3096 in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3085 in
                                                                    uu____3063
                                                                    ::
                                                                    uu____3074 in
                                                                    uu____3041
                                                                    ::
                                                                    uu____3052 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3030 in
                                                                    uu____3008
                                                                    ::
                                                                    uu____3019 in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____2997 in
                                                                    uu____2975
                                                                    ::
                                                                    uu____2986 in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____2964 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____2953 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____2942 in
                                                                    uu____2920
                                                                    ::
                                                                    uu____2931 in
                                                                  uu____2898
                                                                    ::
                                                                    uu____2909 in
                                                                (FStar_Getopt.noshort,
                                                                  "load",
                                                                  (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                  "Load compiled module")
                                                                  ::
                                                                  uu____2887 in
                                                              uu____2865 ::
                                                                uu____2876 in
                                                            (FStar_Getopt.noshort,
                                                              "initial_ifuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                              :: uu____2854 in
                                                          (FStar_Getopt.noshort,
                                                            "initial_fuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of recursive functions to try initially (default 2)")
                                                            :: uu____2843 in
                                                        uu____2821 ::
                                                          uu____2832 in
                                                      (FStar_Getopt.noshort,
                                                        "include",
                                                        (ReverseAccumulated
                                                           (PathStr "path")),
                                                        "A directory in which to search for files included on the command line")
                                                        :: uu____2810 in
                                                    uu____2788 :: uu____2799 in
                                                  uu____2766 :: uu____2777 in
                                                uu____2744 :: uu____2755 in
                                              (FStar_Getopt.noshort,
                                                "hint_file",
                                                (PathStr "path"),
                                                "Read/write hints to <path> (instead of module-specific hints files)")
                                                :: uu____2733 in
                                            uu____2711 :: uu____2722 in
                                          (FStar_Getopt.noshort,
                                            "gen_native_tactics",
                                            (PathStr "[path]"),
                                            "Compile all user tactics used in the module in <path>")
                                            :: uu____2700 in
                                        (FStar_Getopt.noshort, "fstar_home",
                                          (PathStr "dir"),
                                          "Set the FSTAR_HOME variable to <dir>")
                                          :: uu____2689 in
                                      uu____2667 :: uu____2678 in
                                    (FStar_Getopt.noshort,
                                      "extract_namespace",
                                      (Accumulated
                                         (PostProcessed
                                            (pp_lowercase,
                                              (SimpleStr "namespace name")))),
                                      "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                      :: uu____2656 in
                                  (FStar_Getopt.noshort, "extract_module",
                                    (Accumulated
                                       (PostProcessed
                                          (pp_lowercase,
                                            (SimpleStr "module_name")))),
                                    "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                    :: uu____2645 in
                                (FStar_Getopt.noshort, "extract",
                                  (Accumulated
                                     (SimpleStr
                                        "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                  "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                  :: uu____2634 in
                              uu____2612 :: uu____2623 in
                            (FStar_Getopt.noshort, "dump_module",
                              (Accumulated (SimpleStr "module_name")), "") ::
                              uu____2601 in
                          uu____2579 :: uu____2590 in
                        uu____2557 :: uu____2568 in
                      uu____2535 :: uu____2546 in
                    (FStar_Getopt.noshort, "dep",
                      (EnumStr ["make"; "graph"; "full"]),
                      "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                      :: uu____2524 in
                  (FStar_Getopt.noshort, "debug_level",
                    (Accumulated
                       (OpenEnumStr
                          (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                    "Control the verbosity of debugging info") :: uu____2513 in
                (FStar_Getopt.noshort, "debug",
                  (Accumulated (SimpleStr "module_name")),
                  "Print lots of debugging information while checking module")
                  :: uu____2502 in
              (FStar_Getopt.noshort, "codegen-lib",
                (Accumulated (SimpleStr "namespace")),
                "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                :: uu____2491 in
            (FStar_Getopt.noshort, "codegen",
              (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "tactics"]),
              "Generate code for execution") :: uu____2480 in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2469 in
        uu____2447 :: uu____2458 in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2436 in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2425
and specs: Prims.unit -> FStar_Getopt.opt Prims.list =
  fun uu____4631  ->
    let uu____4634 = specs_with_types () in
    FStar_List.map
      (fun uu____4659  ->
         match uu____4659 with
         | (short,long,typ,doc) ->
             let uu____4672 =
               let uu____4683 = arg_spec_of_opt_type long typ in
               (short, long, uu____4683, doc) in
             mk_spec uu____4672) uu____4634
let settable: Prims.string -> Prims.bool =
  fun uu___41_4690  ->
    match uu___41_4690 with
    | "admit_smt_queries" -> true
    | "admit_except" -> true
    | "debug" -> true
    | "debug_level" -> true
    | "detail_errors" -> true
    | "detail_hint_replay" -> true
    | "eager_inference" -> true
    | "hide_uvar_nums" -> true
    | "hint_info" -> true
    | "hint_file" -> true
    | "initial_fuel" -> true
    | "initial_ifuel" -> true
    | "lax" -> true
    | "load" -> true
    | "log_types" -> true
    | "log_queries" -> true
    | "max_fuel" -> true
    | "max_ifuel" -> true
    | "min_fuel" -> true
    | "ugly" -> true
    | "print_bound_var_types" -> true
    | "print_effect_args" -> true
    | "print_full_names" -> true
    | "print_implicits" -> true
    | "print_universes" -> true
    | "print_z3_statistics" -> true
    | "prn" -> true
    | "query_stats" -> true
    | "silent" -> true
    | "smtencoding.elim_box" -> true
    | "smtencoding.nl_arith_repr" -> true
    | "smtencoding.l_arith_repr" -> true
    | "timing" -> true
    | "trace_error" -> true
    | "unthrottle_inductives" -> true
    | "use_eq_at_higher_order" -> true
    | "no_tactics" -> true
    | "normalize_pure_terms_for_extraction" -> true
    | "tactic_raw_binders" -> true
    | "tactic_trace" -> true
    | "tactic_trace_d" -> true
    | "__temp_no_proj" -> true
    | "reuse_hint_for" -> true
    | "warn_error" -> true
    | "z3rlimit_factor" -> true
    | "z3rlimit" -> true
    | "z3refresh" -> true
    | "use_two_phase_tc" -> true
    | "vcgen.optimize_bind_as_seq" -> true
    | uu____4691 -> false
let resettable: Prims.string -> Prims.bool =
  fun s  ->
    (((settable s) || (s = "z3seed")) || (s = "z3cliopt")) ||
      (s = "using_facts_from")
let all_specs: FStar_Getopt.opt Prims.list = specs ()
let all_specs_with_types:
  (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list
  = specs_with_types ()
let settable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____4748  ->
          match uu____4748 with
          | (uu____4759,x,uu____4761,uu____4762) -> settable x))
let resettable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____4808  ->
          match uu____4808 with
          | (uu____4819,x,uu____4821,uu____4822) -> resettable x))
let display_usage: Prims.unit -> Prims.unit =
  fun uu____4829  ->
    let uu____4830 = specs () in display_usage_aux uu____4830
let fstar_home: Prims.unit -> Prims.string =
  fun uu____4845  ->
    let uu____4846 = get_fstar_home () in
    match uu____4846 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        ((let uu____4852 =
            let uu____4857 = mk_string x1 in ("fstar_home", uu____4857) in
          set_option' uu____4852);
         x1)
    | FStar_Pervasives_Native.Some x -> x
exception File_argument of Prims.string
let uu___is_File_argument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____4865 -> true
    | uu____4866 -> false
let __proj__File_argument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____4873 -> uu____4873
let set_options: options -> Prims.string -> FStar_Getopt.parse_cmdline_res =
  fun o  ->
    fun s  ->
      let specs1 =
        match o with
        | Set  -> settable_specs
        | Reset  -> resettable_specs
        | Restore  -> all_specs in
      try
        if s = ""
        then FStar_Getopt.Success
        else
          FStar_Getopt.parse_string specs1
            (fun s1  -> FStar_Exn.raise (File_argument s1)) s
      with
      | File_argument s1 ->
          let uu____4917 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____4917
let file_list_: Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let parse_cmd_line:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____4943  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____4948 =
             let uu____4951 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____4951 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____4948) in
    let uu____5000 =
      let uu____5003 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5003 in
    (res, uu____5000)
let file_list: Prims.unit -> Prims.string Prims.list =
  fun uu____5035  -> FStar_ST.op_Bang file_list_
let restore_cmd_line_options: Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____5068 = specs () in
       FStar_Getopt.parse_cmdline uu____5068 (fun x  -> ()) in
     (let uu____5074 =
        let uu____5079 =
          let uu____5080 = FStar_List.map mk_string old_verify_module in
          List uu____5080 in
        ("verify_module", uu____5079) in
      set_option' uu____5074);
     r)
let module_name_of_file_name: Prims.string -> Prims.string =
  fun f  ->
    let f1 = FStar_Util.basename f in
    let f2 =
      let uu____5088 =
        let uu____5089 =
          let uu____5090 =
            let uu____5091 = FStar_Util.get_file_extension f1 in
            FStar_String.length uu____5091 in
          (FStar_String.length f1) - uu____5090 in
        uu____5089 - (Prims.parse_int "1") in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5088 in
    FStar_String.lowercase f2
let should_verify: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5095 = get_lax () in
    if uu____5095
    then false
    else
      (let l = get_verify_module () in
       FStar_List.contains (FStar_String.lowercase m) l)
let should_verify_file: Prims.string -> Prims.bool =
  fun fn  ->
    let uu____5103 = module_name_of_file_name fn in should_verify uu____5103
let dont_gen_projectors: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5107 = get___temp_no_proj () in
    FStar_List.contains m uu____5107
let should_print_message: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5113 = should_verify m in
    if uu____5113 then m <> "Prims" else false
let include_path: Prims.unit -> Prims.string Prims.list =
  fun uu____5119  ->
    let uu____5120 = get_no_default_includes () in
    if uu____5120
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____5128 =
         let uu____5131 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____5131
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____5144 =
         let uu____5147 = get_include () in
         FStar_List.append uu____5147 ["."] in
       FStar_List.append uu____5128 uu____5144)
let find_file: Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____5155 = FStar_Util.is_path_absolute filename in
    if uu____5155
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5162 =
         let uu____5165 = include_path () in FStar_List.rev uu____5165 in
       FStar_Util.find_map uu____5162
         (fun p  ->
            let path =
              if p = "." then filename else FStar_Util.join_paths p filename in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
let prims: Prims.unit -> Prims.string =
  fun uu____5178  ->
    let uu____5179 = get_prims () in
    match uu____5179 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst" in
        let uu____5183 = find_file filename in
        (match uu____5183 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5187 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename in
             failwith uu____5187)
    | FStar_Pervasives_Native.Some x -> x
let prims_basename: Prims.unit -> Prims.string =
  fun uu____5191  ->
    let uu____5192 = prims () in FStar_Util.basename uu____5192
let pervasives: Prims.unit -> Prims.string =
  fun uu____5195  ->
    let filename = "FStar.Pervasives.fst" in
    let uu____5197 = find_file filename in
    match uu____5197 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5201 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5201
let pervasives_basename: Prims.unit -> Prims.string =
  fun uu____5204  ->
    let uu____5205 = pervasives () in FStar_Util.basename uu____5205
let pervasives_native_basename: Prims.unit -> Prims.string =
  fun uu____5208  ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____5210 = find_file filename in
    match uu____5210 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5214 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5214
let prepend_output_dir: Prims.string -> Prims.string =
  fun fname  ->
    let uu____5218 = get_odir () in
    match uu____5218 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
let prepend_cache_dir: Prims.string -> Prims.string =
  fun fpath  ->
    let uu____5225 = get_cache_dir () in
    match uu____5225 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____5229 = FStar_Util.basename fpath in
        FStar_Util.join_paths x uu____5229
let parse_settings:
  Prims.string Prims.list ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list
  =
  fun ns  ->
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if FStar_Util.starts_with s "-"
        then
          (let path =
             let uu____5281 =
               FStar_Util.substring_from s (Prims.parse_int "1") in
             FStar_Ident.path_of_text uu____5281 in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s in
           ((FStar_Ident.path_of_text s1), true)) in
    let uu____5289 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting))) in
    FStar_All.pipe_right uu____5289 FStar_List.rev
let __temp_no_proj: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5357 = get___temp_no_proj () in
    FStar_All.pipe_right uu____5357 (FStar_List.contains s)
let admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____5364  -> get_admit_smt_queries ()
let admit_except: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5369  -> get_admit_except ()
let cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____5372  -> get_cache_checked_modules ()
let codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5377  -> get_codegen ()
let codegen_libs: Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____5384  ->
    let uu____5385 = get_codegen_lib () in
    FStar_All.pipe_right uu____5385
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
let debug_any: Prims.unit -> Prims.bool =
  fun uu____5400  -> let uu____5401 = get_debug () in uu____5401 <> []
let debug_at_level: Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      (let uu____5414 = get_debug () in
       FStar_All.pipe_right uu____5414 (FStar_List.contains modul)) &&
        (debug_level_geq level)
let dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5423  -> get_dep ()
let detail_errors: Prims.unit -> Prims.bool =
  fun uu____5426  -> get_detail_errors ()
let detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____5429  -> get_detail_hint_replay ()
let doc: Prims.unit -> Prims.bool = fun uu____5432  -> get_doc ()
let dump_module: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5436 = get_dump_module () in
    FStar_All.pipe_right uu____5436 (FStar_List.contains s)
let eager_inference: Prims.unit -> Prims.bool =
  fun uu____5443  -> get_eager_inference ()
let expose_interfaces: Prims.unit -> Prims.bool =
  fun uu____5446  -> get_expose_interfaces ()
let fs_typ_app: Prims.string -> Prims.bool =
  fun filename  ->
    let uu____5450 = FStar_ST.op_Bang light_off_files in
    FStar_List.contains filename uu____5450
let gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5480  -> get_gen_native_tactics ()
let full_context_dependency: Prims.unit -> Prims.bool =
  fun uu____5483  -> true
let hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____5486  -> get_hide_uvar_nums ()
let hint_info: Prims.unit -> Prims.bool =
  fun uu____5489  -> (get_hint_info ()) || (get_query_stats ())
let hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5494  -> get_hint_file ()
let ide: Prims.unit -> Prims.bool = fun uu____5497  -> get_ide ()
let indent: Prims.unit -> Prims.bool = fun uu____5500  -> get_indent ()
let initial_fuel: Prims.unit -> Prims.int =
  fun uu____5503  ->
    let uu____5504 = get_initial_fuel () in
    let uu____5505 = get_max_fuel () in Prims.min uu____5504 uu____5505
let initial_ifuel: Prims.unit -> Prims.int =
  fun uu____5508  ->
    let uu____5509 = get_initial_ifuel () in
    let uu____5510 = get_max_ifuel () in Prims.min uu____5509 uu____5510
let interactive: Prims.unit -> Prims.bool =
  fun uu____5513  -> (get_in ()) || (get_ide ())
let lax: Prims.unit -> Prims.bool = fun uu____5516  -> get_lax ()
let load: Prims.unit -> Prims.string Prims.list =
  fun uu____5521  -> get_load ()
let legacy_interactive: Prims.unit -> Prims.bool =
  fun uu____5524  -> get_in ()
let log_queries: Prims.unit -> Prims.bool =
  fun uu____5527  -> get_log_queries ()
let log_types: Prims.unit -> Prims.bool = fun uu____5530  -> get_log_types ()
let max_fuel: Prims.unit -> Prims.int = fun uu____5533  -> get_max_fuel ()
let max_ifuel: Prims.unit -> Prims.int = fun uu____5536  -> get_max_ifuel ()
let min_fuel: Prims.unit -> Prims.int = fun uu____5539  -> get_min_fuel ()
let ml_ish: Prims.unit -> Prims.bool = fun uu____5542  -> get_MLish ()
let set_ml_ish: Prims.unit -> Prims.unit =
  fun uu____5545  -> set_option "MLish" (Bool true)
let n_cores: Prims.unit -> Prims.int = fun uu____5548  -> get_n_cores ()
let no_default_includes: Prims.unit -> Prims.bool =
  fun uu____5551  -> get_no_default_includes ()
let no_extract: Prims.string -> Prims.bool =
  fun s  ->
    let s1 = FStar_String.lowercase s in
    let uu____5556 = get_no_extract () in
    FStar_All.pipe_right uu____5556
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
let normalize_pure_terms_for_extraction: Prims.unit -> Prims.bool =
  fun uu____5565  -> get_normalize_pure_terms_for_extraction ()
let no_location_info: Prims.unit -> Prims.bool =
  fun uu____5568  -> get_no_location_info ()
let output_dir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5573  -> get_odir ()
let ugly: Prims.unit -> Prims.bool = fun uu____5576  -> get_ugly ()
let print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____5579  -> get_print_bound_var_types ()
let print_effect_args: Prims.unit -> Prims.bool =
  fun uu____5582  -> get_print_effect_args ()
let print_implicits: Prims.unit -> Prims.bool =
  fun uu____5585  -> get_print_implicits ()
let print_real_names: Prims.unit -> Prims.bool =
  fun uu____5588  -> (get_prn ()) || (get_print_full_names ())
let print_universes: Prims.unit -> Prims.bool =
  fun uu____5591  -> get_print_universes ()
let print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____5594  -> (get_print_z3_statistics ()) || (get_query_stats ())
let query_stats: Prims.unit -> Prims.bool =
  fun uu____5597  -> get_query_stats ()
let record_hints: Prims.unit -> Prims.bool =
  fun uu____5600  -> get_record_hints ()
let reuse_hint_for: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____5605  -> get_reuse_hint_for ()
let silent: Prims.unit -> Prims.bool = fun uu____5608  -> get_silent ()
let smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____5611  -> get_smtencoding_elim_box ()
let smtencoding_nl_arith_native: Prims.unit -> Prims.bool =
  fun uu____5614  ->
    let uu____5615 = get_smtencoding_nl_arith_repr () in
    uu____5615 = "native"
let smtencoding_nl_arith_wrapped: Prims.unit -> Prims.bool =
  fun uu____5618  ->
    let uu____5619 = get_smtencoding_nl_arith_repr () in
    uu____5619 = "wrapped"
let smtencoding_nl_arith_default: Prims.unit -> Prims.bool =
  fun uu____5622  ->
    let uu____5623 = get_smtencoding_nl_arith_repr () in
    uu____5623 = "boxwrap"
let smtencoding_l_arith_native: Prims.unit -> Prims.bool =
  fun uu____5626  ->
    let uu____5627 = get_smtencoding_l_arith_repr () in uu____5627 = "native"
let smtencoding_l_arith_default: Prims.unit -> Prims.bool =
  fun uu____5630  ->
    let uu____5631 = get_smtencoding_l_arith_repr () in
    uu____5631 = "boxwrap"
let tactic_raw_binders: Prims.unit -> Prims.bool =
  fun uu____5634  -> get_tactic_raw_binders ()
let tactic_trace: Prims.unit -> Prims.bool =
  fun uu____5637  -> get_tactic_trace ()
let tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____5640  -> get_tactic_trace_d ()
let timing: Prims.unit -> Prims.bool = fun uu____5643  -> get_timing ()
let trace_error: Prims.unit -> Prims.bool =
  fun uu____5646  -> get_trace_error ()
let unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____5649  -> get_unthrottle_inductives ()
let unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____5652  -> get_unsafe_tactic_exec ()
let use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____5655  -> get_use_eq_at_higher_order ()
let use_hints: Prims.unit -> Prims.bool = fun uu____5658  -> get_use_hints ()
let use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____5661  -> get_use_hint_hashes ()
let use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5666  -> get_use_native_tactics ()
let use_tactics: Prims.unit -> Prims.bool =
  fun uu____5669  -> get_use_tactics ()
let using_facts_from:
  Prims.unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5678  ->
    let uu____5679 = get_using_facts_from () in
    match uu____5679 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
let vcgen_optimize_bind_as_seq: Prims.unit -> Prims.bool =
  fun uu____5713  ->
    let uu____5714 = get_vcgen_optimize_bind_as_seq () in
    FStar_Option.isSome uu____5714
let vcgen_decorate_with_type: Prims.unit -> Prims.bool =
  fun uu____5719  ->
    let uu____5720 = get_vcgen_optimize_bind_as_seq () in
    match uu____5720 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____5723 -> false
let warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____5728  -> get_warn_default_effects ()
let z3_exe: Prims.unit -> Prims.string =
  fun uu____5731  ->
    let uu____5732 = get_smt () in
    match uu____5732 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let z3_cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____5740  -> get_z3cliopt ()
let z3_refresh: Prims.unit -> Prims.bool =
  fun uu____5743  -> get_z3refresh ()
let z3_rlimit: Prims.unit -> Prims.int = fun uu____5746  -> get_z3rlimit ()
let z3_rlimit_factor: Prims.unit -> Prims.int =
  fun uu____5749  -> get_z3rlimit_factor ()
let z3_seed: Prims.unit -> Prims.int = fun uu____5752  -> get_z3seed ()
let use_two_phase_tc: Prims.unit -> Prims.bool =
  fun uu____5755  -> get_use_two_phase_tc ()
let no_positivity: Prims.unit -> Prims.bool =
  fun uu____5758  -> get_no_positivity ()
let ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____5761  -> get_ml_no_eta_expand_coertions ()
let warn_error: Prims.unit -> Prims.string =
  fun uu____5764  -> get_warn_error ()
let should_extract: Prims.string -> Prims.bool =
  fun m  ->
    let m1 = FStar_String.lowercase m in
    let uu____5769 = get_extract () in
    match uu____5769 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____5780 =
            let uu____5793 = get_no_extract () in
            let uu____5796 = get_extract_namespace () in
            let uu____5799 = get_extract_module () in
            (uu____5793, uu____5796, uu____5799) in
          match uu____5780 with
          | ([],[],[]) -> ()
          | uu____5814 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting in
          let m_components = FStar_Ident.path_of_text m1 in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____5858,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____5877 -> false in
          let uu____5886 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____5920  ->
                    match uu____5920 with
                    | (path,uu____5928) -> matches_path m_components path)) in
          match uu____5886 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____5939,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____5957 = get_extract_namespace () in
          match uu____5957 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1))) in
        let should_extract_module m2 =
          let uu____5971 = get_extract_module () in
          match uu____5971 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2)) in
        (let uu____5983 = no_extract m1 in Prims.op_Negation uu____5983) &&
          (let uu____5985 =
             let uu____5994 = get_extract_namespace () in
             let uu____5997 = get_extract_module () in
             (uu____5994, uu____5997) in
           (match uu____5985 with
            | ([],[]) -> true
            | uu____6008 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
let codegen_fsharp: Prims.unit -> Prims.bool =
  fun uu____6019  ->
    let uu____6020 = codegen () in
    uu____6020 = (FStar_Pervasives_Native.Some "FSharp")