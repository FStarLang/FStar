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
  fun uu___34_232  ->
    match uu___34_232 with
    | Bool b -> b
    | uu____234 -> failwith "Impos: expected Bool"
let as_int: option_val -> Prims.int =
  fun uu___35_237  ->
    match uu___35_237 with
    | Int b -> b
    | uu____239 -> failwith "Impos: expected Int"
let as_string: option_val -> Prims.string =
  fun uu___36_242  ->
    match uu___36_242 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____245 -> failwith "Impos: expected String"
let as_list': option_val -> option_val Prims.list =
  fun uu___37_250  ->
    match uu___37_250 with
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
    fun uu___38_301  ->
      match uu___38_301 with
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
  fun uu___39_1495  ->
    match uu___39_1495 with
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
  fun p  ->
    let pp = as_string p in
    FStar_Util.mkdir false pp; FStar_Util.mkdir false "pp/cache"; p
let pp_lowercase: option_val -> option_val =
  fun s  ->
    let uu____2390 =
      let uu____2391 = as_string s in FStar_String.lowercase uu____2391 in
    mk_string uu____2390
let rec specs_with_types:
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun uu____2408  ->
    let uu____2419 =
      let uu____2430 =
        let uu____2441 =
          let uu____2450 = let uu____2451 = mk_bool true in Const uu____2451 in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2450,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying") in
        let uu____2452 =
          let uu____2463 =
            let uu____2474 =
              let uu____2485 =
                let uu____2496 =
                  let uu____2507 =
                    let uu____2518 =
                      let uu____2529 =
                        let uu____2538 =
                          let uu____2539 = mk_bool true in Const uu____2539 in
                        (FStar_Getopt.noshort, "detail_errors", uu____2538,
                          "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1") in
                      let uu____2540 =
                        let uu____2551 =
                          let uu____2560 =
                            let uu____2561 = mk_bool true in Const uu____2561 in
                          (FStar_Getopt.noshort, "detail_hint_replay",
                            uu____2560,
                            "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1") in
                        let uu____2562 =
                          let uu____2573 =
                            let uu____2582 =
                              let uu____2583 = mk_bool true in
                              Const uu____2583 in
                            (FStar_Getopt.noshort, "doc", uu____2582,
                              "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.") in
                          let uu____2584 =
                            let uu____2595 =
                              let uu____2606 =
                                let uu____2615 =
                                  let uu____2616 = mk_bool true in
                                  Const uu____2616 in
                                (FStar_Getopt.noshort, "eager_inference",
                                  uu____2615,
                                  "Solve all type-inference constraints eagerly; more efficient but at the cost of generality") in
                              let uu____2617 =
                                let uu____2628 =
                                  let uu____2639 =
                                    let uu____2650 =
                                      let uu____2661 =
                                        let uu____2670 =
                                          let uu____2671 = mk_bool true in
                                          Const uu____2671 in
                                        (FStar_Getopt.noshort,
                                          "expose_interfaces", uu____2670,
                                          "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)") in
                                      let uu____2672 =
                                        let uu____2683 =
                                          let uu____2694 =
                                            let uu____2705 =
                                              let uu____2714 =
                                                let uu____2715 = mk_bool true in
                                                Const uu____2715 in
                                              (FStar_Getopt.noshort,
                                                "hide_uvar_nums", uu____2714,
                                                "Don't print unification variable numbers") in
                                            let uu____2716 =
                                              let uu____2727 =
                                                let uu____2738 =
                                                  let uu____2747 =
                                                    let uu____2748 =
                                                      mk_bool true in
                                                    Const uu____2748 in
                                                  (FStar_Getopt.noshort,
                                                    "hint_info", uu____2747,
                                                    "Print information regarding hints (deprecated; use --query_stats instead)") in
                                                let uu____2749 =
                                                  let uu____2760 =
                                                    let uu____2769 =
                                                      let uu____2770 =
                                                        mk_bool true in
                                                      Const uu____2770 in
                                                    (FStar_Getopt.noshort,
                                                      "in", uu____2769,
                                                      "Legacy interactive mode; reads input from stdin") in
                                                  let uu____2771 =
                                                    let uu____2782 =
                                                      let uu____2791 =
                                                        let uu____2792 =
                                                          mk_bool true in
                                                        Const uu____2792 in
                                                      (FStar_Getopt.noshort,
                                                        "ide", uu____2791,
                                                        "JSON-based interactive mode for IDEs") in
                                                    let uu____2793 =
                                                      let uu____2804 =
                                                        let uu____2815 =
                                                          let uu____2824 =
                                                            let uu____2825 =
                                                              mk_bool true in
                                                            Const uu____2825 in
                                                          (FStar_Getopt.noshort,
                                                            "indent",
                                                            uu____2824,
                                                            "Parses and outputs the files on the command line") in
                                                        let uu____2826 =
                                                          let uu____2837 =
                                                            let uu____2848 =
                                                              let uu____2859
                                                                =
                                                                let uu____2868
                                                                  =
                                                                  let uu____2869
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                  Const
                                                                    uu____2869 in
                                                                (FStar_Getopt.noshort,
                                                                  "lax",
                                                                  uu____2868,
                                                                  "Run the lax-type checker only (admit all verification conditions)") in
                                                              let uu____2870
                                                                =
                                                                let uu____2881
                                                                  =
                                                                  let uu____2892
                                                                    =
                                                                    let uu____2901
                                                                    =
                                                                    let uu____2902
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2902 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____2901,
                                                                    "Print types computed for data/val/let-bindings") in
                                                                  let uu____2903
                                                                    =
                                                                    let uu____2914
                                                                    =
                                                                    let uu____2923
                                                                    =
                                                                    let uu____2924
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2924 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____2923,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go") in
                                                                    let uu____2925
                                                                    =
                                                                    let uu____2936
                                                                    =
                                                                    let uu____2947
                                                                    =
                                                                    let uu____2958
                                                                    =
                                                                    let uu____2969
                                                                    =
                                                                    let uu____2978
                                                                    =
                                                                    let uu____2979
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2979 in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____2978,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)") in
                                                                    let uu____2980
                                                                    =
                                                                    let uu____2991
                                                                    =
                                                                    let uu____3002
                                                                    =
                                                                    let uu____3011
                                                                    =
                                                                    let uu____3012
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3012 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3011,
                                                                    "Ignore the default module search paths") in
                                                                    let uu____3013
                                                                    =
                                                                    let uu____3024
                                                                    =
                                                                    let uu____3035
                                                                    =
                                                                    let uu____3044
                                                                    =
                                                                    let uu____3045
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3045 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3044,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)") in
                                                                    let uu____3046
                                                                    =
                                                                    let uu____3057
                                                                    =
                                                                    let uu____3068
                                                                    =
                                                                    let uu____3079
                                                                    =
                                                                    let uu____3088
                                                                    =
                                                                    let uu____3089
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3089 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3088,
                                                                    "Print the types of bound variables") in
                                                                    let uu____3090
                                                                    =
                                                                    let uu____3101
                                                                    =
                                                                    let uu____3110
                                                                    =
                                                                    let uu____3111
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3111 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3110,
                                                                    "Print inferred predicate transformers for all computation types") in
                                                                    let uu____3112
                                                                    =
                                                                    let uu____3123
                                                                    =
                                                                    let uu____3132
                                                                    =
                                                                    let uu____3133
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3133 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3132,
                                                                    "Print full names of variables") in
                                                                    let uu____3134
                                                                    =
                                                                    let uu____3145
                                                                    =
                                                                    let uu____3154
                                                                    =
                                                                    let uu____3155
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3155 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3154,
                                                                    "Print implicit arguments") in
                                                                    let uu____3156
                                                                    =
                                                                    let uu____3167
                                                                    =
                                                                    let uu____3176
                                                                    =
                                                                    let uu____3177
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3177 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3176,
                                                                    "Print universes") in
                                                                    let uu____3178
                                                                    =
                                                                    let uu____3189
                                                                    =
                                                                    let uu____3198
                                                                    =
                                                                    let uu____3199
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3199 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3198,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)") in
                                                                    let uu____3200
                                                                    =
                                                                    let uu____3211
                                                                    =
                                                                    let uu____3220
                                                                    =
                                                                    let uu____3221
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3221 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3220,
                                                                    "Print full names (deprecated; use --print_full_names instead)") in
                                                                    let uu____3222
                                                                    =
                                                                    let uu____3233
                                                                    =
                                                                    let uu____3242
                                                                    =
                                                                    let uu____3243
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3243 in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3242,
                                                                    "Print SMT query statistics") in
                                                                    let uu____3244
                                                                    =
                                                                    let uu____3255
                                                                    =
                                                                    let uu____3264
                                                                    =
                                                                    let uu____3265
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3265 in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3264,
                                                                    "Record a database of hints for efficient proof replay") in
                                                                    let uu____3266
                                                                    =
                                                                    let uu____3277
                                                                    =
                                                                    let uu____3288
                                                                    =
                                                                    let uu____3297
                                                                    =
                                                                    let uu____3298
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3298 in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3297,
                                                                    " ") in
                                                                    let uu____3299
                                                                    =
                                                                    let uu____3310
                                                                    =
                                                                    let uu____3321
                                                                    =
                                                                    let uu____3332
                                                                    =
                                                                    let uu____3343
                                                                    =
                                                                    let uu____3354
                                                                    =
                                                                    let uu____3363
                                                                    =
                                                                    let uu____3364
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3364 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____3363,
                                                                    "Do not use the lexical scope of tactics to improve binder names") in
                                                                    let uu____3365
                                                                    =
                                                                    let uu____3376
                                                                    =
                                                                    let uu____3385
                                                                    =
                                                                    let uu____3386
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3386 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3385,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)") in
                                                                    let uu____3387
                                                                    =
                                                                    let uu____3398
                                                                    =
                                                                    let uu____3409
                                                                    =
                                                                    let uu____3418
                                                                    =
                                                                    let uu____3419
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3419 in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3418,
                                                                    "Print the time it takes to verify each top-level definition") in
                                                                    let uu____3420
                                                                    =
                                                                    let uu____3431
                                                                    =
                                                                    let uu____3440
                                                                    =
                                                                    let uu____3441
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3441 in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3440,
                                                                    "Don't print an error message; show an exception trace instead") in
                                                                    let uu____3442
                                                                    =
                                                                    let uu____3453
                                                                    =
                                                                    let uu____3462
                                                                    =
                                                                    let uu____3463
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3463 in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3462,
                                                                    "Emit output formatted for debugging") in
                                                                    let uu____3464
                                                                    =
                                                                    let uu____3475
                                                                    =
                                                                    let uu____3484
                                                                    =
                                                                    let uu____3485
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3485 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____3484,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)") in
                                                                    let uu____3486
                                                                    =
                                                                    let uu____3497
                                                                    =
                                                                    let uu____3506
                                                                    =
                                                                    let uu____3507
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3507 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____3506,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.") in
                                                                    let uu____3508
                                                                    =
                                                                    let uu____3519
                                                                    =
                                                                    let uu____3528
                                                                    =
                                                                    let uu____3529
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3529 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____3528,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)") in
                                                                    let uu____3530
                                                                    =
                                                                    let uu____3541
                                                                    =
                                                                    let uu____3550
                                                                    =
                                                                    let uu____3551
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3551 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____3550,
                                                                    "Use a previously recorded hints database for proof replay") in
                                                                    let uu____3552
                                                                    =
                                                                    let uu____3563
                                                                    =
                                                                    let uu____3572
                                                                    =
                                                                    let uu____3573
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3573 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____3572,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database") in
                                                                    let uu____3574
                                                                    =
                                                                    let uu____3585
                                                                    =
                                                                    let uu____3596
                                                                    =
                                                                    let uu____3605
                                                                    =
                                                                    let uu____3606
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3606 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____3605,
                                                                    "Do not run the tactic engine before discharging a VC") in
                                                                    let uu____3607
                                                                    =
                                                                    let uu____3618
                                                                    =
                                                                    let uu____3629
                                                                    =
                                                                    let uu____3640
                                                                    =
                                                                    let uu____3651
                                                                    =
                                                                    let uu____3661
                                                                    =
                                                                    let uu____3662
                                                                    =
                                                                    let uu____3669
                                                                    =
                                                                    let uu____3670
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3670 in
                                                                    ((fun
                                                                    uu____3675
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____3669) in
                                                                    WithSideEffect
                                                                    uu____3662 in
                                                                    (118,
                                                                    "version",
                                                                    uu____3661,
                                                                    "Display version number") in
                                                                    let uu____3679
                                                                    =
                                                                    let uu____3691
                                                                    =
                                                                    let uu____3700
                                                                    =
                                                                    let uu____3701
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3701 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____3700,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)") in
                                                                    let uu____3702
                                                                    =
                                                                    let uu____3713
                                                                    =
                                                                    let uu____3724
                                                                    =
                                                                    let uu____3733
                                                                    =
                                                                    let uu____3734
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3734 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____3733,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness") in
                                                                    let uu____3735
                                                                    =
                                                                    let uu____3746
                                                                    =
                                                                    let uu____3757
                                                                    =
                                                                    let uu____3768
                                                                    =
                                                                    let uu____3779
                                                                    =
                                                                    let uu____3790
                                                                    =
                                                                    let uu____3799
                                                                    =
                                                                    let uu____3800
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3800 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____3799,
                                                                    "Don't check positivity of inductive types") in
                                                                    let uu____3801
                                                                    =
                                                                    let uu____3812
                                                                    =
                                                                    let uu____3821
                                                                    =
                                                                    let uu____3822
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3822 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____3821,
                                                                    "Do not eta-expand coertions in generated OCaml") in
                                                                    let uu____3823
                                                                    =
                                                                    let uu____3834
                                                                    =
                                                                    let uu____3845
                                                                    =
                                                                    let uu____3855
                                                                    =
                                                                    let uu____3856
                                                                    =
                                                                    let uu____3863
                                                                    =
                                                                    let uu____3864
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3864 in
                                                                    ((fun
                                                                    uu____3869
                                                                     ->
                                                                    (
                                                                    let uu____3871
                                                                    =
                                                                    specs () in
                                                                    display_usage_aux
                                                                    uu____3871);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____3863) in
                                                                    WithSideEffect
                                                                    uu____3856 in
                                                                    (104,
                                                                    "help",
                                                                    uu____3855,
                                                                    "Display this information") in
                                                                    [uu____3845] in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____3834 in
                                                                    uu____3812
                                                                    ::
                                                                    uu____3823 in
                                                                    uu____3790
                                                                    ::
                                                                    uu____3801 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'false')")
                                                                    ::
                                                                    uu____3779 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____3768 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____3757 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____3746 in
                                                                    uu____3724
                                                                    ::
                                                                    uu____3735 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____3713 in
                                                                    uu____3691
                                                                    ::
                                                                    uu____3702 in
                                                                    uu____3651
                                                                    ::
                                                                    uu____3679 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____3640 in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____3629 in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____3618 in
                                                                    uu____3596
                                                                    ::
                                                                    uu____3607 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____3585 in
                                                                    uu____3563
                                                                    ::
                                                                    uu____3574 in
                                                                    uu____3541
                                                                    ::
                                                                    uu____3552 in
                                                                    uu____3519
                                                                    ::
                                                                    uu____3530 in
                                                                    uu____3497
                                                                    ::
                                                                    uu____3508 in
                                                                    uu____3475
                                                                    ::
                                                                    uu____3486 in
                                                                    uu____3453
                                                                    ::
                                                                    uu____3464 in
                                                                    uu____3431
                                                                    ::
                                                                    uu____3442 in
                                                                    uu____3409
                                                                    ::
                                                                    uu____3420 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3398 in
                                                                    uu____3376
                                                                    ::
                                                                    uu____3387 in
                                                                    uu____3354
                                                                    ::
                                                                    uu____3365 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3343 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3332 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3321 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3310 in
                                                                    uu____3288
                                                                    ::
                                                                    uu____3299 in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3277 in
                                                                    uu____3255
                                                                    ::
                                                                    uu____3266 in
                                                                    uu____3233
                                                                    ::
                                                                    uu____3244 in
                                                                    uu____3211
                                                                    ::
                                                                    uu____3222 in
                                                                    uu____3189
                                                                    ::
                                                                    uu____3200 in
                                                                    uu____3167
                                                                    ::
                                                                    uu____3178 in
                                                                    uu____3145
                                                                    ::
                                                                    uu____3156 in
                                                                    uu____3123
                                                                    ::
                                                                    uu____3134 in
                                                                    uu____3101
                                                                    ::
                                                                    uu____3112 in
                                                                    uu____3079
                                                                    ::
                                                                    uu____3090 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3068 in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3057 in
                                                                    uu____3035
                                                                    ::
                                                                    uu____3046 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3024 in
                                                                    uu____3002
                                                                    ::
                                                                    uu____3013 in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____2991 in
                                                                    uu____2969
                                                                    ::
                                                                    uu____2980 in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____2958 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____2947 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____2936 in
                                                                    uu____2914
                                                                    ::
                                                                    uu____2925 in
                                                                  uu____2892
                                                                    ::
                                                                    uu____2903 in
                                                                (FStar_Getopt.noshort,
                                                                  "load",
                                                                  (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                  "Load compiled module")
                                                                  ::
                                                                  uu____2881 in
                                                              uu____2859 ::
                                                                uu____2870 in
                                                            (FStar_Getopt.noshort,
                                                              "initial_ifuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                              :: uu____2848 in
                                                          (FStar_Getopt.noshort,
                                                            "initial_fuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of recursive functions to try initially (default 2)")
                                                            :: uu____2837 in
                                                        uu____2815 ::
                                                          uu____2826 in
                                                      (FStar_Getopt.noshort,
                                                        "include",
                                                        (ReverseAccumulated
                                                           (PathStr "path")),
                                                        "A directory in which to search for files included on the command line")
                                                        :: uu____2804 in
                                                    uu____2782 :: uu____2793 in
                                                  uu____2760 :: uu____2771 in
                                                uu____2738 :: uu____2749 in
                                              (FStar_Getopt.noshort,
                                                "hint_file",
                                                (PathStr "path"),
                                                "Read/write hints to <path> (instead of module-specific hints files)")
                                                :: uu____2727 in
                                            uu____2705 :: uu____2716 in
                                          (FStar_Getopt.noshort,
                                            "gen_native_tactics",
                                            (PathStr "[path]"),
                                            "Compile all user tactics used in the module in <path>")
                                            :: uu____2694 in
                                        (FStar_Getopt.noshort, "fstar_home",
                                          (PathStr "dir"),
                                          "Set the FSTAR_HOME variable to <dir>")
                                          :: uu____2683 in
                                      uu____2661 :: uu____2672 in
                                    (FStar_Getopt.noshort,
                                      "extract_namespace",
                                      (Accumulated
                                         (PostProcessed
                                            (pp_lowercase,
                                              (SimpleStr "namespace name")))),
                                      "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                      :: uu____2650 in
                                  (FStar_Getopt.noshort, "extract_module",
                                    (Accumulated
                                       (PostProcessed
                                          (pp_lowercase,
                                            (SimpleStr "module_name")))),
                                    "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                    :: uu____2639 in
                                (FStar_Getopt.noshort, "extract",
                                  (Accumulated
                                     (SimpleStr
                                        "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                  "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                  :: uu____2628 in
                              uu____2606 :: uu____2617 in
                            (FStar_Getopt.noshort, "dump_module",
                              (Accumulated (SimpleStr "module_name")), "") ::
                              uu____2595 in
                          uu____2573 :: uu____2584 in
                        uu____2551 :: uu____2562 in
                      uu____2529 :: uu____2540 in
                    (FStar_Getopt.noshort, "dep",
                      (EnumStr ["make"; "graph"; "full"]),
                      "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                      :: uu____2518 in
                  (FStar_Getopt.noshort, "debug_level",
                    (Accumulated
                       (OpenEnumStr
                          (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                    "Control the verbosity of debugging info") :: uu____2507 in
                (FStar_Getopt.noshort, "debug",
                  (Accumulated (SimpleStr "module_name")),
                  "Print lots of debugging information while checking module")
                  :: uu____2496 in
              (FStar_Getopt.noshort, "codegen-lib",
                (Accumulated (SimpleStr "namespace")),
                "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                :: uu____2485 in
            (FStar_Getopt.noshort, "codegen",
              (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "tactics"]),
              "Generate code for execution") :: uu____2474 in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2463 in
        uu____2441 :: uu____2452 in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2430 in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2419
and specs: Prims.unit -> FStar_Getopt.opt Prims.list =
  fun uu____4595  ->
    let uu____4598 = specs_with_types () in
    FStar_List.map
      (fun uu____4623  ->
         match uu____4623 with
         | (short,long,typ,doc) ->
             let uu____4636 =
               let uu____4647 = arg_spec_of_opt_type long typ in
               (short, long, uu____4647, doc) in
             mk_spec uu____4636) uu____4598
let settable: Prims.string -> Prims.bool =
  fun uu___40_4654  ->
    match uu___40_4654 with
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
    | uu____4655 -> false
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
       (fun uu____4712  ->
          match uu____4712 with
          | (uu____4723,x,uu____4725,uu____4726) -> settable x))
let resettable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____4772  ->
          match uu____4772 with
          | (uu____4783,x,uu____4785,uu____4786) -> resettable x))
let display_usage: Prims.unit -> Prims.unit =
  fun uu____4793  ->
    let uu____4794 = specs () in display_usage_aux uu____4794
let fstar_home: Prims.unit -> Prims.string =
  fun uu____4809  ->
    let uu____4810 = get_fstar_home () in
    match uu____4810 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        ((let uu____4816 =
            let uu____4821 = mk_string x1 in ("fstar_home", uu____4821) in
          set_option' uu____4816);
         x1)
    | FStar_Pervasives_Native.Some x -> x
exception File_argument of Prims.string
let uu___is_File_argument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____4829 -> true
    | uu____4830 -> false
let __proj__File_argument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____4837 -> uu____4837
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
          let uu____4881 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____4881
let file_list_: Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let parse_cmd_line:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____4907  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____4912 =
             let uu____4915 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____4915 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____4912) in
    let uu____4964 =
      let uu____4967 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____4967 in
    (res, uu____4964)
let file_list: Prims.unit -> Prims.string Prims.list =
  fun uu____4999  -> FStar_ST.op_Bang file_list_
let restore_cmd_line_options: Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____5032 = specs () in
       FStar_Getopt.parse_cmdline uu____5032 (fun x  -> ()) in
     (let uu____5038 =
        let uu____5043 =
          let uu____5044 = FStar_List.map mk_string old_verify_module in
          List uu____5044 in
        ("verify_module", uu____5043) in
      set_option' uu____5038);
     r)
let module_name_of_file_name: Prims.string -> Prims.string =
  fun f  ->
    let f1 = FStar_Util.basename f in
    let f2 =
      let uu____5052 =
        let uu____5053 =
          let uu____5054 =
            let uu____5055 = FStar_Util.get_file_extension f1 in
            FStar_String.length uu____5055 in
          (FStar_String.length f1) - uu____5054 in
        uu____5053 - (Prims.parse_int "1") in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5052 in
    FStar_String.lowercase f2
let should_verify: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5059 = get_lax () in
    if uu____5059
    then false
    else
      (let l = get_verify_module () in
       FStar_List.contains (FStar_String.lowercase m) l)
let should_verify_file: Prims.string -> Prims.bool =
  fun fn  ->
    let uu____5067 = module_name_of_file_name fn in should_verify uu____5067
let dont_gen_projectors: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5071 = get___temp_no_proj () in
    FStar_List.contains m uu____5071
let should_print_message: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5077 = should_verify m in
    if uu____5077 then m <> "Prims" else false
let include_path: Prims.unit -> Prims.string Prims.list =
  fun uu____5083  ->
    let uu____5084 = get_no_default_includes () in
    if uu____5084
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____5092 =
         let uu____5095 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____5095
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____5108 =
         let uu____5111 = get_include () in
         FStar_List.append uu____5111 ["."] in
       FStar_List.append uu____5092 uu____5108)
let find_file: Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____5119 = FStar_Util.is_path_absolute filename in
    if uu____5119
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5126 =
         let uu____5129 = include_path () in FStar_List.rev uu____5129 in
       FStar_Util.find_map uu____5126
         (fun p  ->
            let path = FStar_Util.join_paths p filename in
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
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
let prepend_cache_dir: Prims.string -> Prims.string =
  fun fpath  ->
    let uu____5188 = get_cache_dir () in
    match uu____5188 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let fname = FStar_Util.basename fpath in
        Prims.strcat x (Prims.strcat "/" fname)
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