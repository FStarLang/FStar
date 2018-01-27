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
  fun uu____1013  ->
    let o = peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let clear: Prims.unit -> Prims.unit =
  fun uu____1028  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50") in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
let _run: Prims.unit = clear ()
let get_option: Prims.string -> option_val =
  fun s  ->
    let uu____1087 =
      let uu____1090 = peek () in FStar_Util.smap_try_find uu____1090 s in
    match uu____1087 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
let lookup_opt:
  'Auu____1097 . Prims.string -> (option_val -> 'Auu____1097) -> 'Auu____1097
  = fun s  -> fun c  -> c (get_option s)
let get_admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____1113  -> lookup_opt "admit_smt_queries" as_bool
let get_admit_except:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1118  -> lookup_opt "admit_except" (as_option as_string)
let get_cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____1123  -> lookup_opt "cache_checked_modules" as_bool
let get_cache_dir: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1128  -> lookup_opt "cache_dir" (as_option as_string)
let get_codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1135  -> lookup_opt "codegen" (as_option as_string)
let get_codegen_lib: Prims.unit -> Prims.string Prims.list =
  fun uu____1142  -> lookup_opt "codegen-lib" (as_list as_string)
let get_debug: Prims.unit -> Prims.string Prims.list =
  fun uu____1149  -> lookup_opt "debug" (as_list as_string)
let get_debug_level: Prims.unit -> Prims.string Prims.list =
  fun uu____1156  -> lookup_opt "debug_level" (as_list as_string)
let get_dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1163  -> lookup_opt "dep" (as_option as_string)
let get_detail_errors: Prims.unit -> Prims.bool =
  fun uu____1168  -> lookup_opt "detail_errors" as_bool
let get_detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____1171  -> lookup_opt "detail_hint_replay" as_bool
let get_doc: Prims.unit -> Prims.bool =
  fun uu____1174  -> lookup_opt "doc" as_bool
let get_dump_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1179  -> lookup_opt "dump_module" (as_list as_string)
let get_eager_inference: Prims.unit -> Prims.bool =
  fun uu____1184  -> lookup_opt "eager_inference" as_bool
let get_expose_interfaces: Prims.unit -> Prims.bool =
  fun uu____1187  -> lookup_opt "expose_interfaces" as_bool
let get_extract:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1194  -> lookup_opt "extract" (as_option (as_list as_string))
let get_extract_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1205  -> lookup_opt "extract_module" (as_list as_string)
let get_extract_namespace: Prims.unit -> Prims.string Prims.list =
  fun uu____1212  -> lookup_opt "extract_namespace" (as_list as_string)
let get_fs_typ_app: Prims.unit -> Prims.bool =
  fun uu____1217  -> lookup_opt "fs_typ_app" as_bool
let get_fstar_home: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1222  -> lookup_opt "fstar_home" (as_option as_string)
let get_gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1229  -> lookup_opt "gen_native_tactics" (as_option as_string)
let get_hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____1234  -> lookup_opt "hide_uvar_nums" as_bool
let get_hint_info: Prims.unit -> Prims.bool =
  fun uu____1237  -> lookup_opt "hint_info" as_bool
let get_hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1242  -> lookup_opt "hint_file" (as_option as_string)
let get_in: Prims.unit -> Prims.bool =
  fun uu____1247  -> lookup_opt "in" as_bool
let get_ide: Prims.unit -> Prims.bool =
  fun uu____1250  -> lookup_opt "ide" as_bool
let get_include: Prims.unit -> Prims.string Prims.list =
  fun uu____1255  -> lookup_opt "include" (as_list as_string)
let get_indent: Prims.unit -> Prims.bool =
  fun uu____1260  -> lookup_opt "indent" as_bool
let get_initial_fuel: Prims.unit -> Prims.int =
  fun uu____1263  -> lookup_opt "initial_fuel" as_int
let get_initial_ifuel: Prims.unit -> Prims.int =
  fun uu____1266  -> lookup_opt "initial_ifuel" as_int
let get_lax: Prims.unit -> Prims.bool =
  fun uu____1269  -> lookup_opt "lax" as_bool
let get_load: Prims.unit -> Prims.string Prims.list =
  fun uu____1274  -> lookup_opt "load" (as_list as_string)
let get_log_queries: Prims.unit -> Prims.bool =
  fun uu____1279  -> lookup_opt "log_queries" as_bool
let get_log_types: Prims.unit -> Prims.bool =
  fun uu____1282  -> lookup_opt "log_types" as_bool
let get_max_fuel: Prims.unit -> Prims.int =
  fun uu____1285  -> lookup_opt "max_fuel" as_int
let get_max_ifuel: Prims.unit -> Prims.int =
  fun uu____1288  -> lookup_opt "max_ifuel" as_int
let get_min_fuel: Prims.unit -> Prims.int =
  fun uu____1291  -> lookup_opt "min_fuel" as_int
let get_MLish: Prims.unit -> Prims.bool =
  fun uu____1294  -> lookup_opt "MLish" as_bool
let get_n_cores: Prims.unit -> Prims.int =
  fun uu____1297  -> lookup_opt "n_cores" as_int
let get_no_default_includes: Prims.unit -> Prims.bool =
  fun uu____1300  -> lookup_opt "no_default_includes" as_bool
let get_no_extract: Prims.unit -> Prims.string Prims.list =
  fun uu____1305  -> lookup_opt "no_extract" (as_list as_string)
let get_no_location_info: Prims.unit -> Prims.bool =
  fun uu____1310  -> lookup_opt "no_location_info" as_bool
let get_odir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1315  -> lookup_opt "odir" (as_option as_string)
let get_ugly: Prims.unit -> Prims.bool =
  fun uu____1320  -> lookup_opt "ugly" as_bool
let get_prims: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1325  -> lookup_opt "prims" (as_option as_string)
let get_print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____1330  -> lookup_opt "print_bound_var_types" as_bool
let get_print_effect_args: Prims.unit -> Prims.bool =
  fun uu____1333  -> lookup_opt "print_effect_args" as_bool
let get_print_full_names: Prims.unit -> Prims.bool =
  fun uu____1336  -> lookup_opt "print_full_names" as_bool
let get_print_implicits: Prims.unit -> Prims.bool =
  fun uu____1339  -> lookup_opt "print_implicits" as_bool
let get_print_universes: Prims.unit -> Prims.bool =
  fun uu____1342  -> lookup_opt "print_universes" as_bool
let get_print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____1345  -> lookup_opt "print_z3_statistics" as_bool
let get_prn: Prims.unit -> Prims.bool =
  fun uu____1348  -> lookup_opt "prn" as_bool
let get_query_stats: Prims.unit -> Prims.bool =
  fun uu____1351  -> lookup_opt "query_stats" as_bool
let get_record_hints: Prims.unit -> Prims.bool =
  fun uu____1354  -> lookup_opt "record_hints" as_bool
let get_reuse_hint_for:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1359  -> lookup_opt "reuse_hint_for" (as_option as_string)
let get_silent: Prims.unit -> Prims.bool =
  fun uu____1364  -> lookup_opt "silent" as_bool
let get_smt: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1369  -> lookup_opt "smt" (as_option as_string)
let get_smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____1374  -> lookup_opt "smtencoding.elim_box" as_bool
let get_smtencoding_nl_arith_repr: Prims.unit -> Prims.string =
  fun uu____1377  -> lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr: Prims.unit -> Prims.string =
  fun uu____1380  -> lookup_opt "smtencoding.l_arith_repr" as_string
let get_tactic_raw_binders: Prims.unit -> Prims.bool =
  fun uu____1383  -> lookup_opt "tactic_raw_binders" as_bool
let get_tactic_trace: Prims.unit -> Prims.bool =
  fun uu____1386  -> lookup_opt "tactic_trace" as_bool
let get_tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____1389  -> lookup_opt "tactic_trace_d" as_int
let get_timing: Prims.unit -> Prims.bool =
  fun uu____1392  -> lookup_opt "timing" as_bool
let get_trace_error: Prims.unit -> Prims.bool =
  fun uu____1395  -> lookup_opt "trace_error" as_bool
let get_unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____1398  -> lookup_opt "unthrottle_inductives" as_bool
let get_unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____1401  -> lookup_opt "unsafe_tactic_exec" as_bool
let get_use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____1404  -> lookup_opt "use_eq_at_higher_order" as_bool
let get_use_hints: Prims.unit -> Prims.bool =
  fun uu____1407  -> lookup_opt "use_hints" as_bool
let get_use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____1410  -> lookup_opt "use_hint_hashes" as_bool
let get_use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1415  -> lookup_opt "use_native_tactics" (as_option as_string)
let get_use_tactics: Prims.unit -> Prims.bool =
  fun uu____1420  ->
    let uu____1421 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____1421
let get_using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1428  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let get_vcgen_optimize_bind_as_seq:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1439  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
let get_verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1446  -> lookup_opt "verify_module" (as_list as_string)
let get___temp_no_proj: Prims.unit -> Prims.string Prims.list =
  fun uu____1453  -> lookup_opt "__temp_no_proj" (as_list as_string)
let get_version: Prims.unit -> Prims.bool =
  fun uu____1458  -> lookup_opt "version" as_bool
let get_warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____1461  -> lookup_opt "warn_default_effects" as_bool
let get_z3cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____1466  -> lookup_opt "z3cliopt" (as_list as_string)
let get_z3refresh: Prims.unit -> Prims.bool =
  fun uu____1471  -> lookup_opt "z3refresh" as_bool
let get_z3rlimit: Prims.unit -> Prims.int =
  fun uu____1474  -> lookup_opt "z3rlimit" as_int
let get_z3rlimit_factor: Prims.unit -> Prims.int =
  fun uu____1477  -> lookup_opt "z3rlimit_factor" as_int
let get_z3seed: Prims.unit -> Prims.int =
  fun uu____1480  -> lookup_opt "z3seed" as_int
let get_use_two_phase_tc: Prims.unit -> Prims.bool =
  fun uu____1483  -> lookup_opt "use_two_phase_tc" as_bool
let get_no_positivity: Prims.unit -> Prims.bool =
  fun uu____1486  -> lookup_opt "__no_positivity" as_bool
let get_ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____1489  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool
let get_warn_error: Prims.unit -> Prims.string =
  fun uu____1492  -> lookup_opt "warn_error" as_string
let dlevel: Prims.string -> debug_level_t =
  fun uu___40_1495  ->
    match uu___40_1495 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let one_debug_level_geq: debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1503 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let debug_level_geq: debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____1507 = get_debug_level () in
    FStar_All.pipe_right uu____1507
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
let universe_include_path_base_dirs: Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"]
let _version: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _platform: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _compiler: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _date: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _commit: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let display_version: Prims.unit -> Prims.unit =
  fun uu____1638  ->
    let uu____1639 =
      let uu____1640 = FStar_ST.op_Bang _version in
      let uu____1660 = FStar_ST.op_Bang _platform in
      let uu____1680 = FStar_ST.op_Bang _compiler in
      let uu____1700 = FStar_ST.op_Bang _date in
      let uu____1720 = FStar_ST.op_Bang _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1640
        uu____1660 uu____1680 uu____1700 uu____1720 in
    FStar_Util.print_string uu____1639
let display_usage_aux:
  'Auu____1743 'Auu____1744 .
    ('Auu____1744,Prims.string,'Auu____1743 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____1791  ->
         match uu____1791 with
         | (uu____1802,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____1813 =
                      let uu____1814 = FStar_Util.colorize_bold flag in
                      FStar_Util.format1 "  --%s\n" uu____1814 in
                    FStar_Util.print_string uu____1813
                  else
                    (let uu____1816 =
                       let uu____1817 = FStar_Util.colorize_bold flag in
                       FStar_Util.format2 "  --%s  %s\n" uu____1817 doc in
                     FStar_Util.print_string uu____1816)
              | FStar_Getopt.OneArg (uu____1818,argname) ->
                  if doc = ""
                  then
                    let uu____1824 =
                      let uu____1825 = FStar_Util.colorize_bold flag in
                      let uu____1826 = FStar_Util.colorize_bold argname in
                      FStar_Util.format2 "  --%s %s\n" uu____1825 uu____1826 in
                    FStar_Util.print_string uu____1824
                  else
                    (let uu____1828 =
                       let uu____1829 = FStar_Util.colorize_bold flag in
                       let uu____1830 = FStar_Util.colorize_bold argname in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____1829
                         uu____1830 doc in
                     FStar_Util.print_string uu____1828))) specs
let mk_spec:
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____1854 = o in
    match uu____1854 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____1884 =
                let uu____1885 = f () in set_option name uu____1885 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____1896 = f x in set_option name uu____1896 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____1910 = lookup_opt name (as_option as_list') in
        FStar_Util.dflt [] uu____1910 in
      mk_list (value :: prev_values)
let reverse_accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let uu____1929 =
        let uu____1932 = lookup_opt name as_list' in
        FStar_List.append uu____1932 [value] in
      mk_list uu____1929
let accumulate_string:
  'Auu____1941 .
    Prims.string ->
      ('Auu____1941 -> Prims.string) -> 'Auu____1941 -> Prims.unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____1959 =
          let uu____1960 =
            let uu____1961 = post_processor value in mk_string uu____1961 in
          accumulated_option name uu____1960 in
        set_option name uu____1959
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
    match projectee with | Const _0 -> true | uu____2039 -> false
let __proj__Const__item___0: opt_type -> option_val =
  fun projectee  -> match projectee with | Const _0 -> _0
let uu___is_IntStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2051 -> false
let __proj__IntStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | IntStr _0 -> _0
let uu___is_BoolStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2062 -> false
let uu___is_PathStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2067 -> false
let __proj__PathStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | PathStr _0 -> _0
let uu___is_SimpleStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2079 -> false
let __proj__SimpleStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0
let uu___is_EnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2093 -> false
let __proj__EnumStr__item___0: opt_type -> Prims.string Prims.list =
  fun projectee  -> match projectee with | EnumStr _0 -> _0
let uu___is_OpenEnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2117 -> false
let __proj__OpenEnumStr__item___0:
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0
let uu___is_PostProcessed: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2153 -> false
let __proj__PostProcessed__item___0:
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0
let uu___is_Accumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2183 -> false
let __proj__Accumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | Accumulated _0 -> _0
let uu___is_ReverseAccumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2195 -> false
let __proj__ReverseAccumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0
let uu___is_WithSideEffect: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2213 -> false
let __proj__WithSideEffect__item___0:
  opt_type ->
    (Prims.unit -> Prims.unit,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | WithSideEffect _0 -> _0
exception InvalidArgument of Prims.string
let uu___is_InvalidArgument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2245 -> true
    | uu____2246 -> false
let __proj__InvalidArgument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2253 -> uu____2253
let rec parse_opt_val: Prims.string -> opt_type -> Prims.string -> option_val
  =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2267 ->
              let uu____2268 = FStar_Util.safe_int_of_string str_val in
              (match uu____2268 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2272 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name) in
              mk_bool uu____2272
          | PathStr uu____2275 -> mk_path str_val
          | SimpleStr uu____2276 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2281 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2294 = parse_opt_val opt_name elem_spec str_val in
              pp uu____2294
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
            let uu____2311 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1 in
            failwith uu____2311
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
    | PostProcessed (uu____2344,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2352,elem_spec) -> desc_of_opt_type elem_spec
let rec arg_spec_of_opt_type:
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ in
      let uu____2371 = desc_of_opt_type typ in
      match uu____2371 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2377  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
let pp_validate_dir: option_val -> option_val =
  fun p  -> let pp = as_string p in FStar_Util.mkdir false pp; p
let pp_lowercase: option_val -> option_val =
  fun s  ->
    let uu____2389 =
      let uu____2390 = as_string s in FStar_String.lowercase uu____2390 in
    mk_string uu____2389
let rec specs_with_types:
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun uu____2407  ->
    let uu____2418 =
      let uu____2429 =
        let uu____2440 =
          let uu____2449 = let uu____2450 = mk_bool true in Const uu____2450 in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2449,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying") in
        let uu____2451 =
          let uu____2462 =
            let uu____2473 =
              let uu____2484 =
                let uu____2495 =
                  let uu____2506 =
                    let uu____2517 =
                      let uu____2528 =
                        let uu____2537 =
                          let uu____2538 = mk_bool true in Const uu____2538 in
                        (FStar_Getopt.noshort, "detail_errors", uu____2537,
                          "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1") in
                      let uu____2539 =
                        let uu____2550 =
                          let uu____2559 =
                            let uu____2560 = mk_bool true in Const uu____2560 in
                          (FStar_Getopt.noshort, "detail_hint_replay",
                            uu____2559,
                            "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1") in
                        let uu____2561 =
                          let uu____2572 =
                            let uu____2581 =
                              let uu____2582 = mk_bool true in
                              Const uu____2582 in
                            (FStar_Getopt.noshort, "doc", uu____2581,
                              "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.") in
                          let uu____2583 =
                            let uu____2594 =
                              let uu____2605 =
                                let uu____2614 =
                                  let uu____2615 = mk_bool true in
                                  Const uu____2615 in
                                (FStar_Getopt.noshort, "eager_inference",
                                  uu____2614,
                                  "Solve all type-inference constraints eagerly; more efficient but at the cost of generality") in
                              let uu____2616 =
                                let uu____2627 =
                                  let uu____2638 =
                                    let uu____2649 =
                                      let uu____2660 =
                                        let uu____2669 =
                                          let uu____2670 = mk_bool true in
                                          Const uu____2670 in
                                        (FStar_Getopt.noshort,
                                          "expose_interfaces", uu____2669,
                                          "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)") in
                                      let uu____2671 =
                                        let uu____2682 =
                                          let uu____2693 =
                                            let uu____2704 =
                                              let uu____2713 =
                                                let uu____2714 = mk_bool true in
                                                Const uu____2714 in
                                              (FStar_Getopt.noshort,
                                                "hide_uvar_nums", uu____2713,
                                                "Don't print unification variable numbers") in
                                            let uu____2715 =
                                              let uu____2726 =
                                                let uu____2737 =
                                                  let uu____2746 =
                                                    let uu____2747 =
                                                      mk_bool true in
                                                    Const uu____2747 in
                                                  (FStar_Getopt.noshort,
                                                    "hint_info", uu____2746,
                                                    "Print information regarding hints (deprecated; use --query_stats instead)") in
                                                let uu____2748 =
                                                  let uu____2759 =
                                                    let uu____2768 =
                                                      let uu____2769 =
                                                        mk_bool true in
                                                      Const uu____2769 in
                                                    (FStar_Getopt.noshort,
                                                      "in", uu____2768,
                                                      "Legacy interactive mode; reads input from stdin") in
                                                  let uu____2770 =
                                                    let uu____2781 =
                                                      let uu____2790 =
                                                        let uu____2791 =
                                                          mk_bool true in
                                                        Const uu____2791 in
                                                      (FStar_Getopt.noshort,
                                                        "ide", uu____2790,
                                                        "JSON-based interactive mode for IDEs") in
                                                    let uu____2792 =
                                                      let uu____2803 =
                                                        let uu____2814 =
                                                          let uu____2823 =
                                                            let uu____2824 =
                                                              mk_bool true in
                                                            Const uu____2824 in
                                                          (FStar_Getopt.noshort,
                                                            "indent",
                                                            uu____2823,
                                                            "Parses and outputs the files on the command line") in
                                                        let uu____2825 =
                                                          let uu____2836 =
                                                            let uu____2847 =
                                                              let uu____2858
                                                                =
                                                                let uu____2867
                                                                  =
                                                                  let uu____2868
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                  Const
                                                                    uu____2868 in
                                                                (FStar_Getopt.noshort,
                                                                  "lax",
                                                                  uu____2867,
                                                                  "Run the lax-type checker only (admit all verification conditions)") in
                                                              let uu____2869
                                                                =
                                                                let uu____2880
                                                                  =
                                                                  let uu____2891
                                                                    =
                                                                    let uu____2900
                                                                    =
                                                                    let uu____2901
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2901 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____2900,
                                                                    "Print types computed for data/val/let-bindings") in
                                                                  let uu____2902
                                                                    =
                                                                    let uu____2913
                                                                    =
                                                                    let uu____2922
                                                                    =
                                                                    let uu____2923
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2923 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____2922,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go") in
                                                                    let uu____2924
                                                                    =
                                                                    let uu____2935
                                                                    =
                                                                    let uu____2946
                                                                    =
                                                                    let uu____2957
                                                                    =
                                                                    let uu____2968
                                                                    =
                                                                    let uu____2977
                                                                    =
                                                                    let uu____2978
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2978 in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____2977,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)") in
                                                                    let uu____2979
                                                                    =
                                                                    let uu____2990
                                                                    =
                                                                    let uu____3001
                                                                    =
                                                                    let uu____3010
                                                                    =
                                                                    let uu____3011
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3011 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3010,
                                                                    "Ignore the default module search paths") in
                                                                    let uu____3012
                                                                    =
                                                                    let uu____3023
                                                                    =
                                                                    let uu____3034
                                                                    =
                                                                    let uu____3043
                                                                    =
                                                                    let uu____3044
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3044 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3043,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)") in
                                                                    let uu____3045
                                                                    =
                                                                    let uu____3056
                                                                    =
                                                                    let uu____3067
                                                                    =
                                                                    let uu____3078
                                                                    =
                                                                    let uu____3087
                                                                    =
                                                                    let uu____3088
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3088 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3087,
                                                                    "Print the types of bound variables") in
                                                                    let uu____3089
                                                                    =
                                                                    let uu____3100
                                                                    =
                                                                    let uu____3109
                                                                    =
                                                                    let uu____3110
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3110 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3109,
                                                                    "Print inferred predicate transformers for all computation types") in
                                                                    let uu____3111
                                                                    =
                                                                    let uu____3122
                                                                    =
                                                                    let uu____3131
                                                                    =
                                                                    let uu____3132
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3132 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3131,
                                                                    "Print full names of variables") in
                                                                    let uu____3133
                                                                    =
                                                                    let uu____3144
                                                                    =
                                                                    let uu____3153
                                                                    =
                                                                    let uu____3154
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3154 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3153,
                                                                    "Print implicit arguments") in
                                                                    let uu____3155
                                                                    =
                                                                    let uu____3166
                                                                    =
                                                                    let uu____3175
                                                                    =
                                                                    let uu____3176
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3176 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3175,
                                                                    "Print universes") in
                                                                    let uu____3177
                                                                    =
                                                                    let uu____3188
                                                                    =
                                                                    let uu____3197
                                                                    =
                                                                    let uu____3198
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3198 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3197,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)") in
                                                                    let uu____3199
                                                                    =
                                                                    let uu____3210
                                                                    =
                                                                    let uu____3219
                                                                    =
                                                                    let uu____3220
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3220 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3219,
                                                                    "Print full names (deprecated; use --print_full_names instead)") in
                                                                    let uu____3221
                                                                    =
                                                                    let uu____3232
                                                                    =
                                                                    let uu____3241
                                                                    =
                                                                    let uu____3242
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3242 in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3241,
                                                                    "Print SMT query statistics") in
                                                                    let uu____3243
                                                                    =
                                                                    let uu____3254
                                                                    =
                                                                    let uu____3263
                                                                    =
                                                                    let uu____3264
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3264 in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3263,
                                                                    "Record a database of hints for efficient proof replay") in
                                                                    let uu____3265
                                                                    =
                                                                    let uu____3276
                                                                    =
                                                                    let uu____3287
                                                                    =
                                                                    let uu____3296
                                                                    =
                                                                    let uu____3297
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3297 in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3296,
                                                                    " ") in
                                                                    let uu____3298
                                                                    =
                                                                    let uu____3309
                                                                    =
                                                                    let uu____3320
                                                                    =
                                                                    let uu____3331
                                                                    =
                                                                    let uu____3342
                                                                    =
                                                                    let uu____3353
                                                                    =
                                                                    let uu____3362
                                                                    =
                                                                    let uu____3363
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3363 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____3362,
                                                                    "Do not use the lexical scope of tactics to improve binder names") in
                                                                    let uu____3364
                                                                    =
                                                                    let uu____3375
                                                                    =
                                                                    let uu____3384
                                                                    =
                                                                    let uu____3385
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3385 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3384,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)") in
                                                                    let uu____3386
                                                                    =
                                                                    let uu____3397
                                                                    =
                                                                    let uu____3408
                                                                    =
                                                                    let uu____3417
                                                                    =
                                                                    let uu____3418
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3418 in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3417,
                                                                    "Print the time it takes to verify each top-level definition") in
                                                                    let uu____3419
                                                                    =
                                                                    let uu____3430
                                                                    =
                                                                    let uu____3439
                                                                    =
                                                                    let uu____3440
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3440 in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3439,
                                                                    "Don't print an error message; show an exception trace instead") in
                                                                    let uu____3441
                                                                    =
                                                                    let uu____3452
                                                                    =
                                                                    let uu____3461
                                                                    =
                                                                    let uu____3462
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3462 in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3461,
                                                                    "Emit output formatted for debugging") in
                                                                    let uu____3463
                                                                    =
                                                                    let uu____3474
                                                                    =
                                                                    let uu____3483
                                                                    =
                                                                    let uu____3484
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3484 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____3483,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)") in
                                                                    let uu____3485
                                                                    =
                                                                    let uu____3496
                                                                    =
                                                                    let uu____3505
                                                                    =
                                                                    let uu____3506
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3506 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____3505,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.") in
                                                                    let uu____3507
                                                                    =
                                                                    let uu____3518
                                                                    =
                                                                    let uu____3527
                                                                    =
                                                                    let uu____3528
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3528 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____3527,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)") in
                                                                    let uu____3529
                                                                    =
                                                                    let uu____3540
                                                                    =
                                                                    let uu____3549
                                                                    =
                                                                    let uu____3550
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3550 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____3549,
                                                                    "Use a previously recorded hints database for proof replay") in
                                                                    let uu____3551
                                                                    =
                                                                    let uu____3562
                                                                    =
                                                                    let uu____3571
                                                                    =
                                                                    let uu____3572
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3572 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____3571,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database") in
                                                                    let uu____3573
                                                                    =
                                                                    let uu____3584
                                                                    =
                                                                    let uu____3595
                                                                    =
                                                                    let uu____3604
                                                                    =
                                                                    let uu____3605
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3605 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____3604,
                                                                    "Do not run the tactic engine before discharging a VC") in
                                                                    let uu____3606
                                                                    =
                                                                    let uu____3617
                                                                    =
                                                                    let uu____3628
                                                                    =
                                                                    let uu____3639
                                                                    =
                                                                    let uu____3650
                                                                    =
                                                                    let uu____3660
                                                                    =
                                                                    let uu____3661
                                                                    =
                                                                    let uu____3668
                                                                    =
                                                                    let uu____3669
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3669 in
                                                                    ((fun
                                                                    uu____3674
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____3668) in
                                                                    WithSideEffect
                                                                    uu____3661 in
                                                                    (118,
                                                                    "version",
                                                                    uu____3660,
                                                                    "Display version number") in
                                                                    let uu____3678
                                                                    =
                                                                    let uu____3690
                                                                    =
                                                                    let uu____3699
                                                                    =
                                                                    let uu____3700
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3700 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____3699,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)") in
                                                                    let uu____3701
                                                                    =
                                                                    let uu____3712
                                                                    =
                                                                    let uu____3723
                                                                    =
                                                                    let uu____3732
                                                                    =
                                                                    let uu____3733
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3733 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____3732,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness") in
                                                                    let uu____3734
                                                                    =
                                                                    let uu____3745
                                                                    =
                                                                    let uu____3756
                                                                    =
                                                                    let uu____3767
                                                                    =
                                                                    let uu____3778
                                                                    =
                                                                    let uu____3789
                                                                    =
                                                                    let uu____3798
                                                                    =
                                                                    let uu____3799
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3799 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____3798,
                                                                    "Don't check positivity of inductive types") in
                                                                    let uu____3800
                                                                    =
                                                                    let uu____3811
                                                                    =
                                                                    let uu____3820
                                                                    =
                                                                    let uu____3821
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3821 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____3820,
                                                                    "Do not eta-expand coertions in generated OCaml") in
                                                                    let uu____3822
                                                                    =
                                                                    let uu____3833
                                                                    =
                                                                    let uu____3844
                                                                    =
                                                                    let uu____3854
                                                                    =
                                                                    let uu____3855
                                                                    =
                                                                    let uu____3862
                                                                    =
                                                                    let uu____3863
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3863 in
                                                                    ((fun
                                                                    uu____3868
                                                                     ->
                                                                    (
                                                                    let uu____3870
                                                                    =
                                                                    specs () in
                                                                    display_usage_aux
                                                                    uu____3870);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____3862) in
                                                                    WithSideEffect
                                                                    uu____3855 in
                                                                    (104,
                                                                    "help",
                                                                    uu____3854,
                                                                    "Display this information") in
                                                                    [uu____3844] in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____3833 in
                                                                    uu____3811
                                                                    ::
                                                                    uu____3822 in
                                                                    uu____3789
                                                                    ::
                                                                    uu____3800 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'false')")
                                                                    ::
                                                                    uu____3778 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____3767 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____3756 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____3745 in
                                                                    uu____3723
                                                                    ::
                                                                    uu____3734 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____3712 in
                                                                    uu____3690
                                                                    ::
                                                                    uu____3701 in
                                                                    uu____3650
                                                                    ::
                                                                    uu____3678 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____3639 in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____3628 in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____3617 in
                                                                    uu____3595
                                                                    ::
                                                                    uu____3606 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____3584 in
                                                                    uu____3562
                                                                    ::
                                                                    uu____3573 in
                                                                    uu____3540
                                                                    ::
                                                                    uu____3551 in
                                                                    uu____3518
                                                                    ::
                                                                    uu____3529 in
                                                                    uu____3496
                                                                    ::
                                                                    uu____3507 in
                                                                    uu____3474
                                                                    ::
                                                                    uu____3485 in
                                                                    uu____3452
                                                                    ::
                                                                    uu____3463 in
                                                                    uu____3430
                                                                    ::
                                                                    uu____3441 in
                                                                    uu____3408
                                                                    ::
                                                                    uu____3419 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3397 in
                                                                    uu____3375
                                                                    ::
                                                                    uu____3386 in
                                                                    uu____3353
                                                                    ::
                                                                    uu____3364 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3342 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3331 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3320 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3309 in
                                                                    uu____3287
                                                                    ::
                                                                    uu____3298 in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3276 in
                                                                    uu____3254
                                                                    ::
                                                                    uu____3265 in
                                                                    uu____3232
                                                                    ::
                                                                    uu____3243 in
                                                                    uu____3210
                                                                    ::
                                                                    uu____3221 in
                                                                    uu____3188
                                                                    ::
                                                                    uu____3199 in
                                                                    uu____3166
                                                                    ::
                                                                    uu____3177 in
                                                                    uu____3144
                                                                    ::
                                                                    uu____3155 in
                                                                    uu____3122
                                                                    ::
                                                                    uu____3133 in
                                                                    uu____3100
                                                                    ::
                                                                    uu____3111 in
                                                                    uu____3078
                                                                    ::
                                                                    uu____3089 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3067 in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3056 in
                                                                    uu____3034
                                                                    ::
                                                                    uu____3045 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3023 in
                                                                    uu____3001
                                                                    ::
                                                                    uu____3012 in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____2990 in
                                                                    uu____2968
                                                                    ::
                                                                    uu____2979 in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____2957 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____2946 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____2935 in
                                                                    uu____2913
                                                                    ::
                                                                    uu____2924 in
                                                                  uu____2891
                                                                    ::
                                                                    uu____2902 in
                                                                (FStar_Getopt.noshort,
                                                                  "load",
                                                                  (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                  "Load compiled module")
                                                                  ::
                                                                  uu____2880 in
                                                              uu____2858 ::
                                                                uu____2869 in
                                                            (FStar_Getopt.noshort,
                                                              "initial_ifuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                              :: uu____2847 in
                                                          (FStar_Getopt.noshort,
                                                            "initial_fuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of recursive functions to try initially (default 2)")
                                                            :: uu____2836 in
                                                        uu____2814 ::
                                                          uu____2825 in
                                                      (FStar_Getopt.noshort,
                                                        "include",
                                                        (ReverseAccumulated
                                                           (PathStr "path")),
                                                        "A directory in which to search for files included on the command line")
                                                        :: uu____2803 in
                                                    uu____2781 :: uu____2792 in
                                                  uu____2759 :: uu____2770 in
                                                uu____2737 :: uu____2748 in
                                              (FStar_Getopt.noshort,
                                                "hint_file",
                                                (PathStr "path"),
                                                "Read/write hints to <path> (instead of module-specific hints files)")
                                                :: uu____2726 in
                                            uu____2704 :: uu____2715 in
                                          (FStar_Getopt.noshort,
                                            "gen_native_tactics",
                                            (PathStr "[path]"),
                                            "Compile all user tactics used in the module in <path>")
                                            :: uu____2693 in
                                        (FStar_Getopt.noshort, "fstar_home",
                                          (PathStr "dir"),
                                          "Set the FSTAR_HOME variable to <dir>")
                                          :: uu____2682 in
                                      uu____2660 :: uu____2671 in
                                    (FStar_Getopt.noshort,
                                      "extract_namespace",
                                      (Accumulated
                                         (PostProcessed
                                            (pp_lowercase,
                                              (SimpleStr "namespace name")))),
                                      "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                      :: uu____2649 in
                                  (FStar_Getopt.noshort, "extract_module",
                                    (Accumulated
                                       (PostProcessed
                                          (pp_lowercase,
                                            (SimpleStr "module_name")))),
                                    "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                    :: uu____2638 in
                                (FStar_Getopt.noshort, "extract",
                                  (Accumulated
                                     (SimpleStr
                                        "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                  "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                  :: uu____2627 in
                              uu____2605 :: uu____2616 in
                            (FStar_Getopt.noshort, "dump_module",
                              (Accumulated (SimpleStr "module_name")), "") ::
                              uu____2594 in
                          uu____2572 :: uu____2583 in
                        uu____2550 :: uu____2561 in
                      uu____2528 :: uu____2539 in
                    (FStar_Getopt.noshort, "dep",
                      (EnumStr ["make"; "graph"; "full"]),
                      "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                      :: uu____2517 in
                  (FStar_Getopt.noshort, "debug_level",
                    (Accumulated
                       (OpenEnumStr
                          (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                    "Control the verbosity of debugging info") :: uu____2506 in
                (FStar_Getopt.noshort, "debug",
                  (Accumulated (SimpleStr "module_name")),
                  "Print lots of debugging information while checking module")
                  :: uu____2495 in
              (FStar_Getopt.noshort, "codegen-lib",
                (Accumulated (SimpleStr "namespace")),
                "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                :: uu____2484 in
            (FStar_Getopt.noshort, "codegen",
              (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "tactics"]),
              "Generate code for execution") :: uu____2473 in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2462 in
        uu____2440 :: uu____2451 in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2429 in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2418
and specs: Prims.unit -> FStar_Getopt.opt Prims.list =
  fun uu____4594  ->
    let uu____4597 = specs_with_types () in
    FStar_List.map
      (fun uu____4622  ->
         match uu____4622 with
         | (short,long,typ,doc) ->
             let uu____4635 =
               let uu____4646 = arg_spec_of_opt_type long typ in
               (short, long, uu____4646, doc) in
             mk_spec uu____4635) uu____4597
let settable: Prims.string -> Prims.bool =
  fun uu___41_4653  ->
    match uu___41_4653 with
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
    | uu____4654 -> false
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
       (fun uu____4711  ->
          match uu____4711 with
          | (uu____4722,x,uu____4724,uu____4725) -> settable x))
let resettable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____4771  ->
          match uu____4771 with
          | (uu____4782,x,uu____4784,uu____4785) -> resettable x))
let display_usage: Prims.unit -> Prims.unit =
  fun uu____4792  ->
    let uu____4793 = specs () in display_usage_aux uu____4793
let fstar_home: Prims.unit -> Prims.string =
  fun uu____4808  ->
    let uu____4809 = get_fstar_home () in
    match uu____4809 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        ((let uu____4815 =
            let uu____4820 = mk_string x1 in ("fstar_home", uu____4820) in
          set_option' uu____4815);
         x1)
    | FStar_Pervasives_Native.Some x -> x
exception File_argument of Prims.string
let uu___is_File_argument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____4828 -> true
    | uu____4829 -> false
let __proj__File_argument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____4836 -> uu____4836
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
          let uu____4880 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____4880
let file_list_: Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let parse_cmd_line:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____4906  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____4911 =
             let uu____4914 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____4914 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____4911) in
    let uu____4963 =
      let uu____4966 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____4966 in
    (res, uu____4963)
let file_list: Prims.unit -> Prims.string Prims.list =
  fun uu____4998  -> FStar_ST.op_Bang file_list_
let restore_cmd_line_options: Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____5031 = specs () in
       FStar_Getopt.parse_cmdline uu____5031 (fun x  -> ()) in
     (let uu____5037 =
        let uu____5042 =
          let uu____5043 = FStar_List.map mk_string old_verify_module in
          List uu____5043 in
        ("verify_module", uu____5042) in
      set_option' uu____5037);
     r)
let module_name_of_file_name: Prims.string -> Prims.string =
  fun f  ->
    let f1 = FStar_Util.basename f in
    let f2 =
      let uu____5051 =
        let uu____5052 =
          let uu____5053 =
            let uu____5054 = FStar_Util.get_file_extension f1 in
            FStar_String.length uu____5054 in
          (FStar_String.length f1) - uu____5053 in
        uu____5052 - (Prims.parse_int "1") in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5051 in
    FStar_String.lowercase f2
let should_verify: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5058 = get_lax () in
    if uu____5058
    then false
    else
      (let l = get_verify_module () in
       FStar_List.contains (FStar_String.lowercase m) l)
let should_verify_file: Prims.string -> Prims.bool =
  fun fn  ->
    let uu____5066 = module_name_of_file_name fn in should_verify uu____5066
let dont_gen_projectors: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5070 = get___temp_no_proj () in
    FStar_List.contains m uu____5070
let should_print_message: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5076 = should_verify m in
    if uu____5076 then m <> "Prims" else false
let include_path: Prims.unit -> Prims.string Prims.list =
  fun uu____5082  ->
    let uu____5083 = get_no_default_includes () in
    if uu____5083
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____5091 =
         let uu____5094 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____5094
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____5107 =
         let uu____5110 = get_include () in
         FStar_List.append uu____5110 ["."] in
       FStar_List.append uu____5091 uu____5107)
let find_file: Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____5118 = FStar_Util.is_path_absolute filename in
    if uu____5118
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5125 =
         let uu____5128 = include_path () in FStar_List.rev uu____5128 in
       FStar_Util.find_map uu____5125
         (fun p  ->
            let path =
              if p = "." then filename else FStar_Util.join_paths p filename in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
let prims: Prims.unit -> Prims.string =
  fun uu____5141  ->
    let uu____5142 = get_prims () in
    match uu____5142 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst" in
        let uu____5146 = find_file filename in
        (match uu____5146 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5150 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename in
             failwith uu____5150)
    | FStar_Pervasives_Native.Some x -> x
let prims_basename: Prims.unit -> Prims.string =
  fun uu____5154  ->
    let uu____5155 = prims () in FStar_Util.basename uu____5155
let pervasives: Prims.unit -> Prims.string =
  fun uu____5158  ->
    let filename = "FStar.Pervasives.fst" in
    let uu____5160 = find_file filename in
    match uu____5160 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5164 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5164
let pervasives_basename: Prims.unit -> Prims.string =
  fun uu____5167  ->
    let uu____5168 = pervasives () in FStar_Util.basename uu____5168
let pervasives_native_basename: Prims.unit -> Prims.string =
  fun uu____5171  ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____5173 = find_file filename in
    match uu____5173 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5177 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5177
let prepend_output_dir: Prims.string -> Prims.string =
  fun fname  ->
    let uu____5181 = get_odir () in
    match uu____5181 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
let prepend_cache_dir: Prims.string -> Prims.string =
  fun fpath  ->
    let uu____5188 = get_cache_dir () in
    match uu____5188 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____5192 = FStar_Util.basename fpath in
        FStar_Util.join_paths x uu____5192
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
             let uu____5244 =
               FStar_Util.substring_from s (Prims.parse_int "1") in
             FStar_Ident.path_of_text uu____5244 in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s in
           ((FStar_Ident.path_of_text s1), true)) in
    let uu____5252 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting))) in
    FStar_All.pipe_right uu____5252 FStar_List.rev
let __temp_no_proj: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5320 = get___temp_no_proj () in
    FStar_All.pipe_right uu____5320 (FStar_List.contains s)
let admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____5327  -> get_admit_smt_queries ()
let admit_except: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5332  -> get_admit_except ()
let cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____5335  -> get_cache_checked_modules ()
let codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5340  -> get_codegen ()
let codegen_libs: Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____5347  ->
    let uu____5348 = get_codegen_lib () in
    FStar_All.pipe_right uu____5348
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
let debug_any: Prims.unit -> Prims.bool =
  fun uu____5363  -> let uu____5364 = get_debug () in uu____5364 <> []
let debug_at_level: Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      (let uu____5377 = get_debug () in
       FStar_All.pipe_right uu____5377 (FStar_List.contains modul)) &&
        (debug_level_geq level)
let dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5386  -> get_dep ()
let detail_errors: Prims.unit -> Prims.bool =
  fun uu____5389  -> get_detail_errors ()
let detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____5392  -> get_detail_hint_replay ()
let doc: Prims.unit -> Prims.bool = fun uu____5395  -> get_doc ()
let dump_module: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5399 = get_dump_module () in
    FStar_All.pipe_right uu____5399 (FStar_List.contains s)
let eager_inference: Prims.unit -> Prims.bool =
  fun uu____5406  -> get_eager_inference ()
let expose_interfaces: Prims.unit -> Prims.bool =
  fun uu____5409  -> get_expose_interfaces ()
let fs_typ_app: Prims.string -> Prims.bool =
  fun filename  ->
    let uu____5413 = FStar_ST.op_Bang light_off_files in
    FStar_List.contains filename uu____5413
let gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5443  -> get_gen_native_tactics ()
let full_context_dependency: Prims.unit -> Prims.bool =
  fun uu____5446  -> true
let hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____5449  -> get_hide_uvar_nums ()
let hint_info: Prims.unit -> Prims.bool =
  fun uu____5452  -> (get_hint_info ()) || (get_query_stats ())
let hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5457  -> get_hint_file ()
let ide: Prims.unit -> Prims.bool = fun uu____5460  -> get_ide ()
let indent: Prims.unit -> Prims.bool = fun uu____5463  -> get_indent ()
let initial_fuel: Prims.unit -> Prims.int =
  fun uu____5466  ->
    let uu____5467 = get_initial_fuel () in
    let uu____5468 = get_max_fuel () in Prims.min uu____5467 uu____5468
let initial_ifuel: Prims.unit -> Prims.int =
  fun uu____5471  ->
    let uu____5472 = get_initial_ifuel () in
    let uu____5473 = get_max_ifuel () in Prims.min uu____5472 uu____5473
let interactive: Prims.unit -> Prims.bool =
  fun uu____5476  -> (get_in ()) || (get_ide ())
let lax: Prims.unit -> Prims.bool = fun uu____5479  -> get_lax ()
let load: Prims.unit -> Prims.string Prims.list =
  fun uu____5484  -> get_load ()
let legacy_interactive: Prims.unit -> Prims.bool =
  fun uu____5487  -> get_in ()
let log_queries: Prims.unit -> Prims.bool =
  fun uu____5490  -> get_log_queries ()
let log_types: Prims.unit -> Prims.bool = fun uu____5493  -> get_log_types ()
let max_fuel: Prims.unit -> Prims.int = fun uu____5496  -> get_max_fuel ()
let max_ifuel: Prims.unit -> Prims.int = fun uu____5499  -> get_max_ifuel ()
let min_fuel: Prims.unit -> Prims.int = fun uu____5502  -> get_min_fuel ()
let ml_ish: Prims.unit -> Prims.bool = fun uu____5505  -> get_MLish ()
let set_ml_ish: Prims.unit -> Prims.unit =
  fun uu____5508  -> set_option "MLish" (Bool true)
let n_cores: Prims.unit -> Prims.int = fun uu____5511  -> get_n_cores ()
let no_default_includes: Prims.unit -> Prims.bool =
  fun uu____5514  -> get_no_default_includes ()
let no_extract: Prims.string -> Prims.bool =
  fun s  ->
    let s1 = FStar_String.lowercase s in
    let uu____5519 = get_no_extract () in
    FStar_All.pipe_right uu____5519
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
let no_location_info: Prims.unit -> Prims.bool =
  fun uu____5528  -> get_no_location_info ()
let output_dir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5533  -> get_odir ()
let ugly: Prims.unit -> Prims.bool = fun uu____5536  -> get_ugly ()
let print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____5539  -> get_print_bound_var_types ()
let print_effect_args: Prims.unit -> Prims.bool =
  fun uu____5542  -> get_print_effect_args ()
let print_implicits: Prims.unit -> Prims.bool =
  fun uu____5545  -> get_print_implicits ()
let print_real_names: Prims.unit -> Prims.bool =
  fun uu____5548  -> (get_prn ()) || (get_print_full_names ())
let print_universes: Prims.unit -> Prims.bool =
  fun uu____5551  -> get_print_universes ()
let print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____5554  -> (get_print_z3_statistics ()) || (get_query_stats ())
let query_stats: Prims.unit -> Prims.bool =
  fun uu____5557  -> get_query_stats ()
let record_hints: Prims.unit -> Prims.bool =
  fun uu____5560  -> get_record_hints ()
let reuse_hint_for: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____5565  -> get_reuse_hint_for ()
let silent: Prims.unit -> Prims.bool = fun uu____5568  -> get_silent ()
let smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____5571  -> get_smtencoding_elim_box ()
let smtencoding_nl_arith_native: Prims.unit -> Prims.bool =
  fun uu____5574  ->
    let uu____5575 = get_smtencoding_nl_arith_repr () in
    uu____5575 = "native"
let smtencoding_nl_arith_wrapped: Prims.unit -> Prims.bool =
  fun uu____5578  ->
    let uu____5579 = get_smtencoding_nl_arith_repr () in
    uu____5579 = "wrapped"
let smtencoding_nl_arith_default: Prims.unit -> Prims.bool =
  fun uu____5582  ->
    let uu____5583 = get_smtencoding_nl_arith_repr () in
    uu____5583 = "boxwrap"
let smtencoding_l_arith_native: Prims.unit -> Prims.bool =
  fun uu____5586  ->
    let uu____5587 = get_smtencoding_l_arith_repr () in uu____5587 = "native"
let smtencoding_l_arith_default: Prims.unit -> Prims.bool =
  fun uu____5590  ->
    let uu____5591 = get_smtencoding_l_arith_repr () in
    uu____5591 = "boxwrap"
let tactic_raw_binders: Prims.unit -> Prims.bool =
  fun uu____5594  -> get_tactic_raw_binders ()
let tactic_trace: Prims.unit -> Prims.bool =
  fun uu____5597  -> get_tactic_trace ()
let tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____5600  -> get_tactic_trace_d ()
let timing: Prims.unit -> Prims.bool = fun uu____5603  -> get_timing ()
let trace_error: Prims.unit -> Prims.bool =
  fun uu____5606  -> get_trace_error ()
let unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____5609  -> get_unthrottle_inductives ()
let unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____5612  -> get_unsafe_tactic_exec ()
let use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____5615  -> get_use_eq_at_higher_order ()
let use_hints: Prims.unit -> Prims.bool = fun uu____5618  -> get_use_hints ()
let use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____5621  -> get_use_hint_hashes ()
let use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5626  -> get_use_native_tactics ()
let use_tactics: Prims.unit -> Prims.bool =
  fun uu____5629  -> get_use_tactics ()
let using_facts_from:
  Prims.unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5638  ->
    let uu____5639 = get_using_facts_from () in
    match uu____5639 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
let vcgen_optimize_bind_as_seq: Prims.unit -> Prims.bool =
  fun uu____5673  ->
    let uu____5674 = get_vcgen_optimize_bind_as_seq () in
    FStar_Option.isSome uu____5674
let vcgen_decorate_with_type: Prims.unit -> Prims.bool =
  fun uu____5679  ->
    let uu____5680 = get_vcgen_optimize_bind_as_seq () in
    match uu____5680 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____5683 -> false
let warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____5688  -> get_warn_default_effects ()
let z3_exe: Prims.unit -> Prims.string =
  fun uu____5691  ->
    let uu____5692 = get_smt () in
    match uu____5692 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let z3_cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____5700  -> get_z3cliopt ()
let z3_refresh: Prims.unit -> Prims.bool =
  fun uu____5703  -> get_z3refresh ()
let z3_rlimit: Prims.unit -> Prims.int = fun uu____5706  -> get_z3rlimit ()
let z3_rlimit_factor: Prims.unit -> Prims.int =
  fun uu____5709  -> get_z3rlimit_factor ()
let z3_seed: Prims.unit -> Prims.int = fun uu____5712  -> get_z3seed ()
let use_two_phase_tc: Prims.unit -> Prims.bool =
  fun uu____5715  -> get_use_two_phase_tc ()
let no_positivity: Prims.unit -> Prims.bool =
  fun uu____5718  -> get_no_positivity ()
let ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____5721  -> get_ml_no_eta_expand_coertions ()
let warn_error: Prims.unit -> Prims.string =
  fun uu____5724  -> get_warn_error ()
let should_extract: Prims.string -> Prims.bool =
  fun m  ->
    let m1 = FStar_String.lowercase m in
    let uu____5729 = get_extract () in
    match uu____5729 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____5740 =
            let uu____5753 = get_no_extract () in
            let uu____5756 = get_extract_namespace () in
            let uu____5759 = get_extract_module () in
            (uu____5753, uu____5756, uu____5759) in
          match uu____5740 with
          | ([],[],[]) -> ()
          | uu____5774 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting in
          let m_components = FStar_Ident.path_of_text m1 in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____5818,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____5837 -> false in
          let uu____5846 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____5880  ->
                    match uu____5880 with
                    | (path,uu____5888) -> matches_path m_components path)) in
          match uu____5846 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____5899,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____5917 = get_extract_namespace () in
          match uu____5917 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1))) in
        let should_extract_module m2 =
          let uu____5931 = get_extract_module () in
          match uu____5931 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2)) in
        (let uu____5943 = no_extract m1 in Prims.op_Negation uu____5943) &&
          (let uu____5945 =
             let uu____5954 = get_extract_namespace () in
             let uu____5957 = get_extract_module () in
             (uu____5954, uu____5957) in
           (match uu____5945 with
            | ([],[]) -> true
            | uu____5968 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
let codegen_fsharp: Prims.unit -> Prims.bool =
  fun uu____5979  ->
    let uu____5980 = codegen () in
    uu____5980 = (FStar_Pervasives_Native.Some "FSharp")