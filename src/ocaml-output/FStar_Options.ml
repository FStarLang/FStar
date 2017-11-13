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
  fun uu____162  -> FStar_ST.op_Bang __unit_tests__
let __set_unit_tests: Prims.unit -> Prims.unit =
  fun uu____211  -> FStar_ST.op_Colon_Equals __unit_tests__ true
let __clear_unit_tests: Prims.unit -> Prims.unit =
  fun uu____260  -> FStar_ST.op_Colon_Equals __unit_tests__ false
let as_bool: option_val -> Prims.bool =
  fun uu___35_309  ->
    match uu___35_309 with
    | Bool b -> b
    | uu____311 -> failwith "Impos: expected Bool"
let as_int: option_val -> Prims.int =
  fun uu___36_314  ->
    match uu___36_314 with
    | Int b -> b
    | uu____316 -> failwith "Impos: expected Int"
let as_string: option_val -> Prims.string =
  fun uu___37_319  ->
    match uu___37_319 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____322 -> failwith "Impos: expected String"
let as_list': option_val -> option_val Prims.list =
  fun uu___38_327  ->
    match uu___38_327 with
    | List ts -> ts
    | uu____333 -> failwith "Impos: expected List"
let as_list:
  'Auu____339 .
    (option_val -> 'Auu____339) -> option_val -> 'Auu____339 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____355 = as_list' x in
      FStar_All.pipe_right uu____355 (FStar_List.map as_t)
let as_option:
  'Auu____365 .
    (option_val -> 'Auu____365) ->
      option_val -> 'Auu____365 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___39_378  ->
      match uu___39_378 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____382 = as_t v1 in FStar_Pervasives_Native.Some uu____382
type optionstate = option_val FStar_Util.smap[@@deriving show]
let fstar_options: optionstate Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let peek: Prims.unit -> optionstate =
  fun uu____400  ->
    let uu____401 = FStar_ST.op_Bang fstar_options in FStar_List.hd uu____401
let pop: Prims.unit -> Prims.unit =
  fun uu____456  ->
    let uu____457 = FStar_ST.op_Bang fstar_options in
    match uu____457 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____510::[] -> failwith "TOO MANY POPS!"
    | uu____511::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
let push: Prims.unit -> Prims.unit =
  fun uu____567  ->
    let uu____568 =
      let uu____571 =
        let uu____574 = peek () in FStar_Util.smap_copy uu____574 in
      let uu____577 = FStar_ST.op_Bang fstar_options in uu____571 ::
        uu____577 in
    FStar_ST.op_Colon_Equals fstar_options uu____568
let set: optionstate -> Prims.unit =
  fun o  ->
    let uu____687 = FStar_ST.op_Bang fstar_options in
    match uu____687 with
    | [] -> failwith "set on empty option stack"
    | uu____740::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
let set_option: Prims.string -> option_val -> Prims.unit =
  fun k  ->
    fun v1  -> let uu____800 = peek () in FStar_Util.smap_add uu____800 k v1
let set_option':
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> Prims.unit =
  fun uu____809  -> match uu____809 with | (k,v1) -> set_option k v1
let with_saved_options: 'a . (Prims.unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f () in pop (); retv)
let light_off_files: Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let add_light_off_file: Prims.string -> Prims.unit =
  fun filename  ->
    let uu____847 =
      let uu____850 = FStar_ST.op_Bang light_off_files in filename ::
        uu____850 in
    FStar_ST.op_Colon_Equals light_off_files uu____847
let defaults:
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 Prims.list =
  [("__temp_no_proj", (List []));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
  ("cache_checked_modules", (Bool false));
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
  ("split_cases", (Int (Prims.parse_int "0")));
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
  ("verify_module", (List []));
  ("warn_default_effects", (Bool false));
  ("z3refresh", (Bool false));
  ("z3rlimit", (Int (Prims.parse_int "5")));
  ("z3rlimit_factor", (Int (Prims.parse_int "1")));
  ("z3seed", (Int (Prims.parse_int "0")));
  ("z3cliopt", (List []));
  ("use_two_phase_tc", (Bool false));
  ("__no_positivity", (Bool false));
  ("__ml_no_eta_expand_coertions", (Bool false))]
let init: Prims.unit -> Prims.unit =
  fun uu____1309  ->
    let o = peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let clear: Prims.unit -> Prims.unit =
  fun uu____1324  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50") in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
let _run: Prims.unit = clear ()
let get_option: Prims.string -> option_val =
  fun s  ->
    let uu____1437 =
      let uu____1440 = peek () in FStar_Util.smap_try_find uu____1440 s in
    match uu____1437 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
let lookup_opt:
  'Auu____1447 . Prims.string -> (option_val -> 'Auu____1447) -> 'Auu____1447
  = fun s  -> fun c  -> c (get_option s)
let get_admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____1463  -> lookup_opt "admit_smt_queries" as_bool
let get_admit_except:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1468  -> lookup_opt "admit_except" (as_option as_string)
let get_cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____1473  -> lookup_opt "cache_checked_modules" as_bool
let get_codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1478  -> lookup_opt "codegen" (as_option as_string)
let get_codegen_lib: Prims.unit -> Prims.string Prims.list =
  fun uu____1485  -> lookup_opt "codegen-lib" (as_list as_string)
let get_debug: Prims.unit -> Prims.string Prims.list =
  fun uu____1492  -> lookup_opt "debug" (as_list as_string)
let get_debug_level: Prims.unit -> Prims.string Prims.list =
  fun uu____1499  -> lookup_opt "debug_level" (as_list as_string)
let get_dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1506  -> lookup_opt "dep" (as_option as_string)
let get_detail_errors: Prims.unit -> Prims.bool =
  fun uu____1511  -> lookup_opt "detail_errors" as_bool
let get_detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____1514  -> lookup_opt "detail_hint_replay" as_bool
let get_doc: Prims.unit -> Prims.bool =
  fun uu____1517  -> lookup_opt "doc" as_bool
let get_dump_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1522  -> lookup_opt "dump_module" (as_list as_string)
let get_eager_inference: Prims.unit -> Prims.bool =
  fun uu____1527  -> lookup_opt "eager_inference" as_bool
let get_expose_interfaces: Prims.unit -> Prims.bool =
  fun uu____1530  -> lookup_opt "expose_interfaces" as_bool
let get_extract_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1535  -> lookup_opt "extract_module" (as_list as_string)
let get_extract_namespace: Prims.unit -> Prims.string Prims.list =
  fun uu____1542  -> lookup_opt "extract_namespace" (as_list as_string)
let get_fs_typ_app: Prims.unit -> Prims.bool =
  fun uu____1547  -> lookup_opt "fs_typ_app" as_bool
let get_fstar_home: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1552  -> lookup_opt "fstar_home" (as_option as_string)
let get_gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1559  -> lookup_opt "gen_native_tactics" (as_option as_string)
let get_hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____1564  -> lookup_opt "hide_uvar_nums" as_bool
let get_hint_info: Prims.unit -> Prims.bool =
  fun uu____1567  -> lookup_opt "hint_info" as_bool
let get_hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1572  -> lookup_opt "hint_file" (as_option as_string)
let get_in: Prims.unit -> Prims.bool =
  fun uu____1577  -> lookup_opt "in" as_bool
let get_ide: Prims.unit -> Prims.bool =
  fun uu____1580  -> lookup_opt "ide" as_bool
let get_include: Prims.unit -> Prims.string Prims.list =
  fun uu____1585  -> lookup_opt "include" (as_list as_string)
let get_indent: Prims.unit -> Prims.bool =
  fun uu____1590  -> lookup_opt "indent" as_bool
let get_initial_fuel: Prims.unit -> Prims.int =
  fun uu____1593  -> lookup_opt "initial_fuel" as_int
let get_initial_ifuel: Prims.unit -> Prims.int =
  fun uu____1596  -> lookup_opt "initial_ifuel" as_int
let get_lax: Prims.unit -> Prims.bool =
  fun uu____1599  -> lookup_opt "lax" as_bool
let get_load: Prims.unit -> Prims.string Prims.list =
  fun uu____1604  -> lookup_opt "load" (as_list as_string)
let get_log_queries: Prims.unit -> Prims.bool =
  fun uu____1609  -> lookup_opt "log_queries" as_bool
let get_log_types: Prims.unit -> Prims.bool =
  fun uu____1612  -> lookup_opt "log_types" as_bool
let get_max_fuel: Prims.unit -> Prims.int =
  fun uu____1615  -> lookup_opt "max_fuel" as_int
let get_max_ifuel: Prims.unit -> Prims.int =
  fun uu____1618  -> lookup_opt "max_ifuel" as_int
let get_min_fuel: Prims.unit -> Prims.int =
  fun uu____1621  -> lookup_opt "min_fuel" as_int
let get_MLish: Prims.unit -> Prims.bool =
  fun uu____1624  -> lookup_opt "MLish" as_bool
let get_n_cores: Prims.unit -> Prims.int =
  fun uu____1627  -> lookup_opt "n_cores" as_int
let get_no_default_includes: Prims.unit -> Prims.bool =
  fun uu____1630  -> lookup_opt "no_default_includes" as_bool
let get_no_extract: Prims.unit -> Prims.string Prims.list =
  fun uu____1635  -> lookup_opt "no_extract" (as_list as_string)
let get_no_location_info: Prims.unit -> Prims.bool =
  fun uu____1640  -> lookup_opt "no_location_info" as_bool
let get_odir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1645  -> lookup_opt "odir" (as_option as_string)
let get_ugly: Prims.unit -> Prims.bool =
  fun uu____1650  -> lookup_opt "ugly" as_bool
let get_prims: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1655  -> lookup_opt "prims" (as_option as_string)
let get_print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____1660  -> lookup_opt "print_bound_var_types" as_bool
let get_print_effect_args: Prims.unit -> Prims.bool =
  fun uu____1663  -> lookup_opt "print_effect_args" as_bool
let get_print_full_names: Prims.unit -> Prims.bool =
  fun uu____1666  -> lookup_opt "print_full_names" as_bool
let get_print_implicits: Prims.unit -> Prims.bool =
  fun uu____1669  -> lookup_opt "print_implicits" as_bool
let get_print_universes: Prims.unit -> Prims.bool =
  fun uu____1672  -> lookup_opt "print_universes" as_bool
let get_print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____1675  -> lookup_opt "print_z3_statistics" as_bool
let get_prn: Prims.unit -> Prims.bool =
  fun uu____1678  -> lookup_opt "prn" as_bool
let get_query_stats: Prims.unit -> Prims.bool =
  fun uu____1681  -> lookup_opt "query_stats" as_bool
let get_record_hints: Prims.unit -> Prims.bool =
  fun uu____1684  -> lookup_opt "record_hints" as_bool
let get_reuse_hint_for:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1689  -> lookup_opt "reuse_hint_for" (as_option as_string)
let get_silent: Prims.unit -> Prims.bool =
  fun uu____1694  -> lookup_opt "silent" as_bool
let get_smt: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1699  -> lookup_opt "smt" (as_option as_string)
let get_smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____1704  -> lookup_opt "smtencoding.elim_box" as_bool
let get_smtencoding_nl_arith_repr: Prims.unit -> Prims.string =
  fun uu____1707  -> lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr: Prims.unit -> Prims.string =
  fun uu____1710  -> lookup_opt "smtencoding.l_arith_repr" as_string
let get_split_cases: Prims.unit -> Prims.int =
  fun uu____1713  -> lookup_opt "split_cases" as_int
let get_tactic_trace: Prims.unit -> Prims.bool =
  fun uu____1716  -> lookup_opt "tactic_trace" as_bool
let get_tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____1719  -> lookup_opt "tactic_trace_d" as_int
let get_timing: Prims.unit -> Prims.bool =
  fun uu____1722  -> lookup_opt "timing" as_bool
let get_trace_error: Prims.unit -> Prims.bool =
  fun uu____1725  -> lookup_opt "trace_error" as_bool
let get_unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____1728  -> lookup_opt "unthrottle_inductives" as_bool
let get_unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____1731  -> lookup_opt "unsafe_tactic_exec" as_bool
let get_use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____1734  -> lookup_opt "use_eq_at_higher_order" as_bool
let get_use_hints: Prims.unit -> Prims.bool =
  fun uu____1737  -> lookup_opt "use_hints" as_bool
let get_use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____1740  -> lookup_opt "use_hint_hashes" as_bool
let get_use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1745  -> lookup_opt "use_native_tactics" (as_option as_string)
let get_use_tactics: Prims.unit -> Prims.bool =
  fun uu____1750  ->
    let uu____1751 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____1751
let get_using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1758  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let get_verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1769  -> lookup_opt "verify_module" (as_list as_string)
let get___temp_no_proj: Prims.unit -> Prims.string Prims.list =
  fun uu____1776  -> lookup_opt "__temp_no_proj" (as_list as_string)
let get_version: Prims.unit -> Prims.bool =
  fun uu____1781  -> lookup_opt "version" as_bool
let get_warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____1784  -> lookup_opt "warn_default_effects" as_bool
let get_z3cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____1789  -> lookup_opt "z3cliopt" (as_list as_string)
let get_z3refresh: Prims.unit -> Prims.bool =
  fun uu____1794  -> lookup_opt "z3refresh" as_bool
let get_z3rlimit: Prims.unit -> Prims.int =
  fun uu____1797  -> lookup_opt "z3rlimit" as_int
let get_z3rlimit_factor: Prims.unit -> Prims.int =
  fun uu____1800  -> lookup_opt "z3rlimit_factor" as_int
let get_z3seed: Prims.unit -> Prims.int =
  fun uu____1803  -> lookup_opt "z3seed" as_int
let get_use_two_phase_tc: Prims.unit -> Prims.bool =
  fun uu____1806  -> lookup_opt "use_two_phase_tc" as_bool
let get_no_positivity: Prims.unit -> Prims.bool =
  fun uu____1809  -> lookup_opt "__no_positivity" as_bool
let get_ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____1812  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool
let dlevel: Prims.string -> debug_level_t =
  fun uu___40_1815  ->
    match uu___40_1815 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let one_debug_level_geq: debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1823 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let debug_level_geq: debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____1827 = get_debug_level () in
    FStar_All.pipe_right uu____1827
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
let universe_include_path_base_dirs: Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"]
let _version: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _platform: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _compiler: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _date: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _commit: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let display_version: Prims.unit -> Prims.unit =
  fun uu____1918  ->
    let uu____1919 =
      let uu____1920 = FStar_ST.op_Bang _version in
      let uu____1967 = FStar_ST.op_Bang _platform in
      let uu____2014 = FStar_ST.op_Bang _compiler in
      let uu____2061 = FStar_ST.op_Bang _date in
      let uu____2108 = FStar_ST.op_Bang _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1920
        uu____1967 uu____2014 uu____2061 uu____2108 in
    FStar_Util.print_string uu____1919
let display_usage_aux:
  'Auu____2158 'Auu____2159 .
    ('Auu____2159,Prims.string,'Auu____2158 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2206  ->
         match uu____2206 with
         | (uu____2217,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2228 =
                      let uu____2229 = FStar_Util.colorize_bold flag in
                      FStar_Util.format1 "  --%s\n" uu____2229 in
                    FStar_Util.print_string uu____2228
                  else
                    (let uu____2231 =
                       let uu____2232 = FStar_Util.colorize_bold flag in
                       FStar_Util.format2 "  --%s  %s\n" uu____2232 doc in
                     FStar_Util.print_string uu____2231)
              | FStar_Getopt.OneArg (uu____2233,argname) ->
                  if doc = ""
                  then
                    let uu____2239 =
                      let uu____2240 = FStar_Util.colorize_bold flag in
                      let uu____2241 = FStar_Util.colorize_bold argname in
                      FStar_Util.format2 "  --%s %s\n" uu____2240 uu____2241 in
                    FStar_Util.print_string uu____2239
                  else
                    (let uu____2243 =
                       let uu____2244 = FStar_Util.colorize_bold flag in
                       let uu____2245 = FStar_Util.colorize_bold argname in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2244
                         uu____2245 doc in
                     FStar_Util.print_string uu____2243))) specs
let mk_spec:
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____2272 = o in
    match uu____2272 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2302 =
                let uu____2303 = f () in set_option name uu____2303 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2314 = f x in set_option name uu____2314 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2334 = lookup_opt name (as_option as_list') in
        FStar_Util.dflt [] uu____2334 in
      mk_list (value :: prev_values)
let reverse_accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let uu____2353 =
        let uu____2356 = lookup_opt name as_list' in
        FStar_List.append uu____2356 [value] in
      mk_list uu____2353
let accumulate_string:
  'Auu____2365 .
    Prims.string ->
      ('Auu____2365 -> Prims.string) -> 'Auu____2365 -> Prims.unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2383 =
          let uu____2384 =
            let uu____2385 = post_processor value in mk_string uu____2385 in
          accumulated_option name uu____2384 in
        set_option name uu____2383
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
    match projectee with | Const _0 -> true | uu____2463 -> false
let __proj__Const__item___0: opt_type -> option_val =
  fun projectee  -> match projectee with | Const _0 -> _0
let uu___is_IntStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2475 -> false
let __proj__IntStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | IntStr _0 -> _0
let uu___is_BoolStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2486 -> false
let uu___is_PathStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2491 -> false
let __proj__PathStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | PathStr _0 -> _0
let uu___is_SimpleStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2503 -> false
let __proj__SimpleStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0
let uu___is_EnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2517 -> false
let __proj__EnumStr__item___0: opt_type -> Prims.string Prims.list =
  fun projectee  -> match projectee with | EnumStr _0 -> _0
let uu___is_OpenEnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2541 -> false
let __proj__OpenEnumStr__item___0:
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0
let uu___is_PostProcessed: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2577 -> false
let __proj__PostProcessed__item___0:
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0
let uu___is_Accumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2607 -> false
let __proj__Accumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | Accumulated _0 -> _0
let uu___is_ReverseAccumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2619 -> false
let __proj__ReverseAccumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0
let uu___is_WithSideEffect: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2637 -> false
let __proj__WithSideEffect__item___0:
  opt_type ->
    (Prims.unit -> Prims.unit,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | WithSideEffect _0 -> _0
exception InvalidArgument of Prims.string
let uu___is_InvalidArgument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2669 -> true
    | uu____2670 -> false
let __proj__InvalidArgument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2677 -> uu____2677
let rec parse_opt_val: Prims.string -> opt_type -> Prims.string -> option_val
  =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2691 ->
              let uu____2692 = FStar_Util.safe_int_of_string str_val in
              (match uu____2692 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2696 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name) in
              mk_bool uu____2696
          | PathStr uu____2699 -> mk_path str_val
          | SimpleStr uu____2700 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2705 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2718 = parse_opt_val opt_name elem_spec str_val in
              pp uu____2718
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
            let uu____2735 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1 in
            failwith uu____2735
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
    | PostProcessed (uu____2768,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2776,elem_spec) -> desc_of_opt_type elem_spec
let rec arg_spec_of_opt_type:
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ in
      let uu____2795 = desc_of_opt_type typ in
      match uu____2795 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2801  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
let pp_validate_dir: option_val -> option_val =
  fun p  -> let pp = as_string p in FStar_Util.mkdir false pp; p
let pp_lowercase: option_val -> option_val =
  fun s  ->
    let uu____2813 =
      let uu____2814 = as_string s in FStar_String.lowercase uu____2814 in
    mk_string uu____2813
let rec specs_with_types:
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun uu____2831  ->
    let uu____2842 =
      let uu____2853 =
        let uu____2864 =
          let uu____2873 = let uu____2874 = mk_bool true in Const uu____2874 in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2873,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying") in
        let uu____2875 =
          let uu____2886 =
            let uu____2897 =
              let uu____2908 =
                let uu____2919 =
                  let uu____2930 =
                    let uu____2941 =
                      let uu____2950 =
                        let uu____2951 = mk_bool true in Const uu____2951 in
                      (FStar_Getopt.noshort, "detail_errors", uu____2950,
                        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1") in
                    let uu____2952 =
                      let uu____2963 =
                        let uu____2972 =
                          let uu____2973 = mk_bool true in Const uu____2973 in
                        (FStar_Getopt.noshort, "detail_hint_replay",
                          uu____2972,
                          "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1") in
                      let uu____2974 =
                        let uu____2985 =
                          let uu____2994 =
                            let uu____2995 = mk_bool true in Const uu____2995 in
                          (FStar_Getopt.noshort, "doc", uu____2994,
                            "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.") in
                        let uu____2996 =
                          let uu____3007 =
                            let uu____3018 =
                              let uu____3027 =
                                let uu____3028 = mk_bool true in
                                Const uu____3028 in
                              (FStar_Getopt.noshort, "eager_inference",
                                uu____3027,
                                "Solve all type-inference constraints eagerly; more efficient but at the cost of generality") in
                            let uu____3029 =
                              let uu____3040 =
                                let uu____3051 =
                                  let uu____3062 =
                                    let uu____3071 =
                                      let uu____3072 = mk_bool true in
                                      Const uu____3072 in
                                    (FStar_Getopt.noshort,
                                      "expose_interfaces", uu____3071,
                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)") in
                                  let uu____3073 =
                                    let uu____3084 =
                                      let uu____3095 =
                                        let uu____3106 =
                                          let uu____3115 =
                                            let uu____3116 = mk_bool true in
                                            Const uu____3116 in
                                          (FStar_Getopt.noshort,
                                            "hide_uvar_nums", uu____3115,
                                            "Don't print unification variable numbers") in
                                        let uu____3117 =
                                          let uu____3128 =
                                            let uu____3139 =
                                              let uu____3148 =
                                                let uu____3149 = mk_bool true in
                                                Const uu____3149 in
                                              (FStar_Getopt.noshort,
                                                "hint_info", uu____3148,
                                                "Print information regarding hints (deprecated; use --query_stats instead)") in
                                            let uu____3150 =
                                              let uu____3161 =
                                                let uu____3170 =
                                                  let uu____3171 =
                                                    mk_bool true in
                                                  Const uu____3171 in
                                                (FStar_Getopt.noshort, "in",
                                                  uu____3170,
                                                  "Legacy interactive mode; reads input from stdin") in
                                              let uu____3172 =
                                                let uu____3183 =
                                                  let uu____3192 =
                                                    let uu____3193 =
                                                      mk_bool true in
                                                    Const uu____3193 in
                                                  (FStar_Getopt.noshort,
                                                    "ide", uu____3192,
                                                    "JSON-based interactive mode for IDEs") in
                                                let uu____3194 =
                                                  let uu____3205 =
                                                    let uu____3216 =
                                                      let uu____3225 =
                                                        let uu____3226 =
                                                          mk_bool true in
                                                        Const uu____3226 in
                                                      (FStar_Getopt.noshort,
                                                        "indent", uu____3225,
                                                        "Parses and outputs the files on the command line") in
                                                    let uu____3227 =
                                                      let uu____3238 =
                                                        let uu____3249 =
                                                          let uu____3260 =
                                                            let uu____3269 =
                                                              let uu____3270
                                                                =
                                                                mk_bool true in
                                                              Const
                                                                uu____3270 in
                                                            (FStar_Getopt.noshort,
                                                              "lax",
                                                              uu____3269,
                                                              "Run the lax-type checker only (admit all verification conditions)") in
                                                          let uu____3271 =
                                                            let uu____3282 =
                                                              let uu____3293
                                                                =
                                                                let uu____3302
                                                                  =
                                                                  let uu____3303
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                  Const
                                                                    uu____3303 in
                                                                (FStar_Getopt.noshort,
                                                                  "log_types",
                                                                  uu____3302,
                                                                  "Print types computed for data/val/let-bindings") in
                                                              let uu____3304
                                                                =
                                                                let uu____3315
                                                                  =
                                                                  let uu____3324
                                                                    =
                                                                    let uu____3325
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3325 in
                                                                  (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3324,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go") in
                                                                let uu____3326
                                                                  =
                                                                  let uu____3337
                                                                    =
                                                                    let uu____3348
                                                                    =
                                                                    let uu____3359
                                                                    =
                                                                    let uu____3370
                                                                    =
                                                                    let uu____3379
                                                                    =
                                                                    let uu____3380
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3380 in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3379,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)") in
                                                                    let uu____3381
                                                                    =
                                                                    let uu____3392
                                                                    =
                                                                    let uu____3403
                                                                    =
                                                                    let uu____3412
                                                                    =
                                                                    let uu____3413
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3413 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3412,
                                                                    "Ignore the default module search paths") in
                                                                    let uu____3414
                                                                    =
                                                                    let uu____3425
                                                                    =
                                                                    let uu____3436
                                                                    =
                                                                    let uu____3445
                                                                    =
                                                                    let uu____3446
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3446 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3445,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)") in
                                                                    let uu____3447
                                                                    =
                                                                    let uu____3458
                                                                    =
                                                                    let uu____3469
                                                                    =
                                                                    let uu____3480
                                                                    =
                                                                    let uu____3489
                                                                    =
                                                                    let uu____3490
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3490 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3489,
                                                                    "Print the types of bound variables") in
                                                                    let uu____3491
                                                                    =
                                                                    let uu____3502
                                                                    =
                                                                    let uu____3511
                                                                    =
                                                                    let uu____3512
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3512 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3511,
                                                                    "Print inferred predicate transformers for all computation types") in
                                                                    let uu____3513
                                                                    =
                                                                    let uu____3524
                                                                    =
                                                                    let uu____3533
                                                                    =
                                                                    let uu____3534
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3534 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3533,
                                                                    "Print full names of variables") in
                                                                    let uu____3535
                                                                    =
                                                                    let uu____3546
                                                                    =
                                                                    let uu____3555
                                                                    =
                                                                    let uu____3556
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3556 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3555,
                                                                    "Print implicit arguments") in
                                                                    let uu____3557
                                                                    =
                                                                    let uu____3568
                                                                    =
                                                                    let uu____3577
                                                                    =
                                                                    let uu____3578
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3578 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3577,
                                                                    "Print universes") in
                                                                    let uu____3579
                                                                    =
                                                                    let uu____3590
                                                                    =
                                                                    let uu____3599
                                                                    =
                                                                    let uu____3600
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3600 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3599,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)") in
                                                                    let uu____3601
                                                                    =
                                                                    let uu____3612
                                                                    =
                                                                    let uu____3621
                                                                    =
                                                                    let uu____3622
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3622 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3621,
                                                                    "Print full names (deprecated; use --print_full_names instead)") in
                                                                    let uu____3623
                                                                    =
                                                                    let uu____3634
                                                                    =
                                                                    let uu____3643
                                                                    =
                                                                    let uu____3644
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3644 in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3643,
                                                                    "Print SMT query statistics") in
                                                                    let uu____3645
                                                                    =
                                                                    let uu____3656
                                                                    =
                                                                    let uu____3665
                                                                    =
                                                                    let uu____3666
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3666 in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3665,
                                                                    "Record a database of hints for efficient proof replay") in
                                                                    let uu____3667
                                                                    =
                                                                    let uu____3678
                                                                    =
                                                                    let uu____3689
                                                                    =
                                                                    let uu____3698
                                                                    =
                                                                    let uu____3699
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3699 in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3698,
                                                                    " ") in
                                                                    let uu____3700
                                                                    =
                                                                    let uu____3711
                                                                    =
                                                                    let uu____3722
                                                                    =
                                                                    let uu____3733
                                                                    =
                                                                    let uu____3744
                                                                    =
                                                                    let uu____3755
                                                                    =
                                                                    let uu____3766
                                                                    =
                                                                    let uu____3775
                                                                    =
                                                                    let uu____3776
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3776 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3775,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)") in
                                                                    let uu____3777
                                                                    =
                                                                    let uu____3788
                                                                    =
                                                                    let uu____3799
                                                                    =
                                                                    let uu____3808
                                                                    =
                                                                    let uu____3809
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3809 in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3808,
                                                                    "Print the time it takes to verify each top-level definition") in
                                                                    let uu____3810
                                                                    =
                                                                    let uu____3821
                                                                    =
                                                                    let uu____3830
                                                                    =
                                                                    let uu____3831
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3831 in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3830,
                                                                    "Don't print an error message; show an exception trace instead") in
                                                                    let uu____3832
                                                                    =
                                                                    let uu____3843
                                                                    =
                                                                    let uu____3852
                                                                    =
                                                                    let uu____3853
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3853 in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3852,
                                                                    "Emit output formatted for debugging") in
                                                                    let uu____3854
                                                                    =
                                                                    let uu____3865
                                                                    =
                                                                    let uu____3874
                                                                    =
                                                                    let uu____3875
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3875 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____3874,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)") in
                                                                    let uu____3876
                                                                    =
                                                                    let uu____3887
                                                                    =
                                                                    let uu____3896
                                                                    =
                                                                    let uu____3897
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3897 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____3896,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.") in
                                                                    let uu____3898
                                                                    =
                                                                    let uu____3909
                                                                    =
                                                                    let uu____3918
                                                                    =
                                                                    let uu____3919
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3919 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____3918,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)") in
                                                                    let uu____3920
                                                                    =
                                                                    let uu____3931
                                                                    =
                                                                    let uu____3940
                                                                    =
                                                                    let uu____3941
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3941 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____3940,
                                                                    "Use a previously recorded hints database for proof replay") in
                                                                    let uu____3942
                                                                    =
                                                                    let uu____3953
                                                                    =
                                                                    let uu____3962
                                                                    =
                                                                    let uu____3963
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3963 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____3962,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database") in
                                                                    let uu____3964
                                                                    =
                                                                    let uu____3975
                                                                    =
                                                                    let uu____3986
                                                                    =
                                                                    let uu____3995
                                                                    =
                                                                    let uu____3996
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3996 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____3995,
                                                                    "Do not run the tactic engine before discharging a VC") in
                                                                    let uu____3997
                                                                    =
                                                                    let uu____4008
                                                                    =
                                                                    let uu____4019
                                                                    =
                                                                    let uu____4030
                                                                    =
                                                                    let uu____4039
                                                                    =
                                                                    let uu____4040
                                                                    =
                                                                    let uu____4047
                                                                    =
                                                                    let uu____4048
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4048 in
                                                                    ((fun
                                                                    uu____4053
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____4047) in
                                                                    WithSideEffect
                                                                    uu____4040 in
                                                                    (118,
                                                                    "version",
                                                                    uu____4039,
                                                                    "Display version number") in
                                                                    let uu____4055
                                                                    =
                                                                    let uu____4066
                                                                    =
                                                                    let uu____4075
                                                                    =
                                                                    let uu____4076
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4076 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4075,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)") in
                                                                    let uu____4077
                                                                    =
                                                                    let uu____4088
                                                                    =
                                                                    let uu____4099
                                                                    =
                                                                    let uu____4108
                                                                    =
                                                                    let uu____4109
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4109 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4108,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness") in
                                                                    let uu____4110
                                                                    =
                                                                    let uu____4121
                                                                    =
                                                                    let uu____4132
                                                                    =
                                                                    let uu____4143
                                                                    =
                                                                    let uu____4154
                                                                    =
                                                                    let uu____4163
                                                                    =
                                                                    let uu____4164
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4164 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    uu____4163,
                                                                    "Use the two phase typechecker") in
                                                                    let uu____4165
                                                                    =
                                                                    let uu____4176
                                                                    =
                                                                    let uu____4185
                                                                    =
                                                                    let uu____4186
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4186 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4185,
                                                                    "Don't check positivity of inductive types") in
                                                                    let uu____4187
                                                                    =
                                                                    let uu____4198
                                                                    =
                                                                    let uu____4207
                                                                    =
                                                                    let uu____4208
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4208 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4207,
                                                                    "Do not eta-expand coertions in generated OCaml") in
                                                                    let uu____4209
                                                                    =
                                                                    let uu____4220
                                                                    =
                                                                    let uu____4229
                                                                    =
                                                                    let uu____4230
                                                                    =
                                                                    let uu____4237
                                                                    =
                                                                    let uu____4238
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4238 in
                                                                    ((fun
                                                                    uu____4243
                                                                     ->
                                                                    (
                                                                    let uu____4245
                                                                    =
                                                                    specs () in
                                                                    display_usage_aux
                                                                    uu____4245);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____4237) in
                                                                    WithSideEffect
                                                                    uu____4230 in
                                                                    (104,
                                                                    "help",
                                                                    uu____4229,
                                                                    "Display this information") in
                                                                    [uu____4220] in
                                                                    uu____4198
                                                                    ::
                                                                    uu____4209 in
                                                                    uu____4176
                                                                    ::
                                                                    uu____4187 in
                                                                    uu____4154
                                                                    ::
                                                                    uu____4165 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4143 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4132 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4121 in
                                                                    uu____4099
                                                                    ::
                                                                    uu____4110 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4088 in
                                                                    uu____4066
                                                                    ::
                                                                    uu____4077 in
                                                                    uu____4030
                                                                    ::
                                                                    uu____4055 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4019 in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4008 in
                                                                    uu____3986
                                                                    ::
                                                                    uu____3997 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____3975 in
                                                                    uu____3953
                                                                    ::
                                                                    uu____3964 in
                                                                    uu____3931
                                                                    ::
                                                                    uu____3942 in
                                                                    uu____3909
                                                                    ::
                                                                    uu____3920 in
                                                                    uu____3887
                                                                    ::
                                                                    uu____3898 in
                                                                    uu____3865
                                                                    ::
                                                                    uu____3876 in
                                                                    uu____3843
                                                                    ::
                                                                    uu____3854 in
                                                                    uu____3821
                                                                    ::
                                                                    uu____3832 in
                                                                    uu____3799
                                                                    ::
                                                                    uu____3810 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3788 in
                                                                    uu____3766
                                                                    ::
                                                                    uu____3777 in
                                                                    (FStar_Getopt.noshort,
                                                                    "split_cases",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Partition VC of a match into groups of <positive_integer> cases")
                                                                    ::
                                                                    uu____3755 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3744 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3733 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3722 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3711 in
                                                                    uu____3689
                                                                    ::
                                                                    uu____3700 in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3678 in
                                                                    uu____3656
                                                                    ::
                                                                    uu____3667 in
                                                                    uu____3634
                                                                    ::
                                                                    uu____3645 in
                                                                    uu____3612
                                                                    ::
                                                                    uu____3623 in
                                                                    uu____3590
                                                                    ::
                                                                    uu____3601 in
                                                                    uu____3568
                                                                    ::
                                                                    uu____3579 in
                                                                    uu____3546
                                                                    ::
                                                                    uu____3557 in
                                                                    uu____3524
                                                                    ::
                                                                    uu____3535 in
                                                                    uu____3502
                                                                    ::
                                                                    uu____3513 in
                                                                    uu____3480
                                                                    ::
                                                                    uu____3491 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3469 in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3458 in
                                                                    uu____3436
                                                                    ::
                                                                    uu____3447 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Do not extract code from this module")
                                                                    ::
                                                                    uu____3425 in
                                                                    uu____3403
                                                                    ::
                                                                    uu____3414 in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3392 in
                                                                    uu____3370
                                                                    ::
                                                                    uu____3381 in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3359 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3348 in
                                                                  (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (
                                                                    IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3337 in
                                                                uu____3315 ::
                                                                  uu____3326 in
                                                              uu____3293 ::
                                                                uu____3304 in
                                                            (FStar_Getopt.noshort,
                                                              "load",
                                                              (ReverseAccumulated
                                                                 (PathStr
                                                                    "module")),
                                                              "Load compiled module")
                                                              :: uu____3282 in
                                                          uu____3260 ::
                                                            uu____3271 in
                                                        (FStar_Getopt.noshort,
                                                          "initial_ifuel",
                                                          (IntStr
                                                             "non-negative integer"),
                                                          "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                          :: uu____3249 in
                                                      (FStar_Getopt.noshort,
                                                        "initial_fuel",
                                                        (IntStr
                                                           "non-negative integer"),
                                                        "Number of unrolling of recursive functions to try initially (default 2)")
                                                        :: uu____3238 in
                                                    uu____3216 :: uu____3227 in
                                                  (FStar_Getopt.noshort,
                                                    "include",
                                                    (ReverseAccumulated
                                                       (PathStr "path")),
                                                    "A directory in which to search for files included on the command line")
                                                    :: uu____3205 in
                                                uu____3183 :: uu____3194 in
                                              uu____3161 :: uu____3172 in
                                            uu____3139 :: uu____3150 in
                                          (FStar_Getopt.noshort, "hint_file",
                                            (PathStr "path"),
                                            "Read/write hints to <path> (instead of module-specific hints files)")
                                            :: uu____3128 in
                                        uu____3106 :: uu____3117 in
                                      (FStar_Getopt.noshort,
                                        "gen_native_tactics",
                                        (PathStr "[path]"),
                                        "Compile all user tactics used in the module in <path>")
                                        :: uu____3095 in
                                    (FStar_Getopt.noshort, "fstar_home",
                                      (PathStr "dir"),
                                      "Set the FSTAR_HOME variable to <dir>")
                                      :: uu____3084 in
                                  uu____3062 :: uu____3073 in
                                (FStar_Getopt.noshort, "extract_namespace",
                                  (Accumulated
                                     (PostProcessed
                                        (pp_lowercase,
                                          (SimpleStr "namespace name")))),
                                  "Only extract modules in the specified namespace")
                                  :: uu____3051 in
                              (FStar_Getopt.noshort, "extract_module",
                                (Accumulated
                                   (PostProcessed
                                      (pp_lowercase,
                                        (SimpleStr "module_name")))),
                                "Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                :: uu____3040 in
                            uu____3018 :: uu____3029 in
                          (FStar_Getopt.noshort, "dump_module",
                            (Accumulated (SimpleStr "module_name")), "") ::
                            uu____3007 in
                        uu____2985 :: uu____2996 in
                      uu____2963 :: uu____2974 in
                    uu____2941 :: uu____2952 in
                  (FStar_Getopt.noshort, "dep",
                    (EnumStr ["make"; "graph"; "full"]),
                    "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                    :: uu____2930 in
                (FStar_Getopt.noshort, "debug_level",
                  (Accumulated
                     (OpenEnumStr
                        (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                  "Control the verbosity of debugging info") :: uu____2919 in
              (FStar_Getopt.noshort, "debug",
                (Accumulated (SimpleStr "module_name")),
                "Print lots of debugging information while checking module")
                :: uu____2908 in
            (FStar_Getopt.noshort, "codegen-lib",
              (Accumulated (SimpleStr "namespace")),
              "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
              :: uu____2897 in
          (FStar_Getopt.noshort, "codegen",
            (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "tactics"]),
            "Generate code for execution") :: uu____2886 in
        uu____2864 :: uu____2875 in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2853 in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2842
and specs: Prims.unit -> FStar_Getopt.opt Prims.list =
  fun uu____4930  ->
    let uu____4933 = specs_with_types () in
    FStar_List.map
      (fun uu____4958  ->
         match uu____4958 with
         | (short,long,typ,doc) ->
             let uu____4971 =
               let uu____4982 = arg_spec_of_opt_type long typ in
               (short, long, uu____4982, doc) in
             mk_spec uu____4971) uu____4933
let settable: Prims.string -> Prims.bool =
  fun uu___41_4995  ->
    match uu___41_4995 with
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
    | "split_cases" -> true
    | "timing" -> true
    | "trace_error" -> true
    | "unthrottle_inductives" -> true
    | "use_eq_at_higher_order" -> true
    | "no_tactics" -> true
    | "tactic_trace" -> true
    | "tactic_trace_d" -> true
    | "__temp_no_proj" -> true
    | "reuse_hint_for" -> true
    | "z3rlimit_factor" -> true
    | "z3rlimit" -> true
    | "z3refresh" -> true
    | "use_two_phase_tc" -> true
    | uu____4996 -> false
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
       (fun uu____5053  ->
          match uu____5053 with
          | (uu____5064,x,uu____5066,uu____5067) -> settable x))
let resettable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5113  ->
          match uu____5113 with
          | (uu____5124,x,uu____5126,uu____5127) -> resettable x))
let display_usage: Prims.unit -> Prims.unit =
  fun uu____5134  ->
    let uu____5135 = specs () in display_usage_aux uu____5135
let fstar_home: Prims.unit -> Prims.string =
  fun uu____5150  ->
    let uu____5151 = get_fstar_home () in
    match uu____5151 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        ((let uu____5157 =
            let uu____5162 = mk_string x1 in ("fstar_home", uu____5162) in
          set_option' uu____5157);
         x1)
    | FStar_Pervasives_Native.Some x -> x
exception File_argument of Prims.string
let uu___is_File_argument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____5170 -> true
    | uu____5171 -> false
let __proj__File_argument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____5178 -> uu____5178
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
          let uu____5222 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____5222
let file_list_: Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let parse_cmd_line:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____5244  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5249 =
             let uu____5252 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____5252 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____5249) in
    let uu____5355 =
      let uu____5358 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5358 in
    (res, uu____5355)
let file_list: Prims.unit -> Prims.string Prims.list =
  fun uu____5417  -> FStar_ST.op_Bang file_list_
let restore_cmd_line_options: Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____5477 = specs () in
       FStar_Getopt.parse_cmdline uu____5477 (fun x  -> ()) in
     (let uu____5483 =
        let uu____5488 =
          let uu____5489 = FStar_List.map mk_string old_verify_module in
          List uu____5489 in
        ("verify_module", uu____5488) in
      set_option' uu____5483);
     r)
let module_name_of_file_name: Prims.string -> Prims.string =
  fun f  ->
    let f1 = FStar_Util.basename f in
    let f2 =
      let uu____5497 =
        let uu____5498 =
          let uu____5499 =
            let uu____5500 = FStar_Util.get_file_extension f1 in
            FStar_String.length uu____5500 in
          (FStar_String.length f1) - uu____5499 in
        uu____5498 - (Prims.parse_int "1") in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5497 in
    FStar_String.lowercase f2
let should_verify: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5504 = get_lax () in
    if uu____5504
    then false
    else
      (let l = get_verify_module () in
       FStar_List.contains (FStar_String.lowercase m) l)
let should_verify_file: Prims.string -> Prims.bool =
  fun fn  ->
    let uu____5512 = module_name_of_file_name fn in should_verify uu____5512
let dont_gen_projectors: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5516 = get___temp_no_proj () in
    FStar_List.contains m uu____5516
let should_print_message: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5522 = should_verify m in
    if uu____5522 then m <> "Prims" else false
let include_path: Prims.unit -> Prims.string Prims.list =
  fun uu____5528  ->
    let uu____5529 = get_no_default_includes () in
    if uu____5529
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____5537 =
         let uu____5540 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____5540
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____5553 =
         let uu____5556 = get_include () in
         FStar_List.append uu____5556 ["."] in
       FStar_List.append uu____5537 uu____5553)
let find_file: Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____5564 = FStar_Util.is_path_absolute filename in
    if uu____5564
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5571 =
         let uu____5574 = include_path () in FStar_List.rev uu____5574 in
       FStar_Util.find_map uu____5571
         (fun p  ->
            let path = FStar_Util.join_paths p filename in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
let prims: Prims.unit -> Prims.string =
  fun uu____5586  ->
    let uu____5587 = get_prims () in
    match uu____5587 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst" in
        let uu____5591 = find_file filename in
        (match uu____5591 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5595 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename in
             failwith uu____5595)
    | FStar_Pervasives_Native.Some x -> x
let prims_basename: Prims.unit -> Prims.string =
  fun uu____5599  ->
    let uu____5600 = prims () in FStar_Util.basename uu____5600
let pervasives: Prims.unit -> Prims.string =
  fun uu____5603  ->
    let filename = "FStar.Pervasives.fst" in
    let uu____5605 = find_file filename in
    match uu____5605 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5609 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5609
let pervasives_basename: Prims.unit -> Prims.string =
  fun uu____5612  ->
    let uu____5613 = pervasives () in FStar_Util.basename uu____5613
let pervasives_native_basename: Prims.unit -> Prims.string =
  fun uu____5616  ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____5618 = find_file filename in
    match uu____5618 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5622 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5622
let prepend_output_dir: Prims.string -> Prims.string =
  fun fname  ->
    let uu____5626 = get_odir () in
    match uu____5626 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
let __temp_no_proj: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5633 = get___temp_no_proj () in
    FStar_All.pipe_right uu____5633 (FStar_List.contains s)
let admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____5640  -> get_admit_smt_queries ()
let admit_except: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5645  -> get_admit_except ()
let cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____5648  -> get_cache_checked_modules ()
let codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5653  -> get_codegen ()
let codegen_libs: Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____5660  ->
    let uu____5661 = get_codegen_lib () in
    FStar_All.pipe_right uu____5661
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
let debug_any: Prims.unit -> Prims.bool =
  fun uu____5676  -> let uu____5677 = get_debug () in uu____5677 <> []
let debug_at_level: Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      (let uu____5690 = get_debug () in
       FStar_All.pipe_right uu____5690 (FStar_List.contains modul)) &&
        (debug_level_geq level)
let dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5699  -> get_dep ()
let detail_errors: Prims.unit -> Prims.bool =
  fun uu____5702  -> get_detail_errors ()
let detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____5705  -> get_detail_hint_replay ()
let doc: Prims.unit -> Prims.bool = fun uu____5708  -> get_doc ()
let dump_module: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5712 = get_dump_module () in
    FStar_All.pipe_right uu____5712 (FStar_List.contains s)
let eager_inference: Prims.unit -> Prims.bool =
  fun uu____5719  -> get_eager_inference ()
let expose_interfaces: Prims.unit -> Prims.bool =
  fun uu____5722  -> get_expose_interfaces ()
let fs_typ_app: Prims.string -> Prims.bool =
  fun filename  ->
    let uu____5726 = FStar_ST.op_Bang light_off_files in
    FStar_List.contains filename uu____5726
let gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5783  -> get_gen_native_tactics ()
let full_context_dependency: Prims.unit -> Prims.bool =
  fun uu____5786  -> true
let hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____5789  -> get_hide_uvar_nums ()
let hint_info: Prims.unit -> Prims.bool =
  fun uu____5792  -> (get_hint_info ()) || (get_query_stats ())
let hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5797  -> get_hint_file ()
let ide: Prims.unit -> Prims.bool = fun uu____5800  -> get_ide ()
let indent: Prims.unit -> Prims.bool = fun uu____5803  -> get_indent ()
let initial_fuel: Prims.unit -> Prims.int =
  fun uu____5806  ->
    let uu____5807 = get_initial_fuel () in
    let uu____5808 = get_max_fuel () in Prims.min uu____5807 uu____5808
let initial_ifuel: Prims.unit -> Prims.int =
  fun uu____5811  ->
    let uu____5812 = get_initial_ifuel () in
    let uu____5813 = get_max_ifuel () in Prims.min uu____5812 uu____5813
let interactive: Prims.unit -> Prims.bool =
  fun uu____5816  -> (get_in ()) || (get_ide ())
let lax: Prims.unit -> Prims.bool = fun uu____5819  -> get_lax ()
let load: Prims.unit -> Prims.string Prims.list =
  fun uu____5824  -> get_load ()
let legacy_interactive: Prims.unit -> Prims.bool =
  fun uu____5827  -> get_in ()
let log_queries: Prims.unit -> Prims.bool =
  fun uu____5830  -> get_log_queries ()
let log_types: Prims.unit -> Prims.bool = fun uu____5833  -> get_log_types ()
let max_fuel: Prims.unit -> Prims.int = fun uu____5836  -> get_max_fuel ()
let max_ifuel: Prims.unit -> Prims.int = fun uu____5839  -> get_max_ifuel ()
let min_fuel: Prims.unit -> Prims.int = fun uu____5842  -> get_min_fuel ()
let ml_ish: Prims.unit -> Prims.bool = fun uu____5845  -> get_MLish ()
let set_ml_ish: Prims.unit -> Prims.unit =
  fun uu____5848  -> set_option "MLish" (Bool true)
let n_cores: Prims.unit -> Prims.int = fun uu____5851  -> get_n_cores ()
let no_default_includes: Prims.unit -> Prims.bool =
  fun uu____5854  -> get_no_default_includes ()
let no_extract: Prims.string -> Prims.bool =
  fun s  ->
    let s1 = FStar_String.lowercase s in
    let uu____5859 = get_no_extract () in
    FStar_All.pipe_right uu____5859
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
let no_location_info: Prims.unit -> Prims.bool =
  fun uu____5868  -> get_no_location_info ()
let output_dir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5873  -> get_odir ()
let ugly: Prims.unit -> Prims.bool = fun uu____5876  -> get_ugly ()
let print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____5879  -> get_print_bound_var_types ()
let print_effect_args: Prims.unit -> Prims.bool =
  fun uu____5882  -> get_print_effect_args ()
let print_implicits: Prims.unit -> Prims.bool =
  fun uu____5885  -> get_print_implicits ()
let print_real_names: Prims.unit -> Prims.bool =
  fun uu____5888  -> (get_prn ()) || (get_print_full_names ())
let print_universes: Prims.unit -> Prims.bool =
  fun uu____5891  -> get_print_universes ()
let print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____5894  -> (get_print_z3_statistics ()) || (get_query_stats ())
let query_stats: Prims.unit -> Prims.bool =
  fun uu____5897  -> get_query_stats ()
let record_hints: Prims.unit -> Prims.bool =
  fun uu____5900  -> get_record_hints ()
let reuse_hint_for: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____5905  -> get_reuse_hint_for ()
let silent: Prims.unit -> Prims.bool = fun uu____5908  -> get_silent ()
let smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____5911  -> get_smtencoding_elim_box ()
let smtencoding_nl_arith_native: Prims.unit -> Prims.bool =
  fun uu____5914  ->
    let uu____5915 = get_smtencoding_nl_arith_repr () in
    uu____5915 = "native"
let smtencoding_nl_arith_wrapped: Prims.unit -> Prims.bool =
  fun uu____5918  ->
    let uu____5919 = get_smtencoding_nl_arith_repr () in
    uu____5919 = "wrapped"
let smtencoding_nl_arith_default: Prims.unit -> Prims.bool =
  fun uu____5922  ->
    let uu____5923 = get_smtencoding_nl_arith_repr () in
    uu____5923 = "boxwrap"
let smtencoding_l_arith_native: Prims.unit -> Prims.bool =
  fun uu____5926  ->
    let uu____5927 = get_smtencoding_l_arith_repr () in uu____5927 = "native"
let smtencoding_l_arith_default: Prims.unit -> Prims.bool =
  fun uu____5930  ->
    let uu____5931 = get_smtencoding_l_arith_repr () in
    uu____5931 = "boxwrap"
let split_cases: Prims.unit -> Prims.int =
  fun uu____5934  -> get_split_cases ()
let tactic_trace: Prims.unit -> Prims.bool =
  fun uu____5937  -> get_tactic_trace ()
let tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____5940  -> get_tactic_trace_d ()
let timing: Prims.unit -> Prims.bool = fun uu____5943  -> get_timing ()
let trace_error: Prims.unit -> Prims.bool =
  fun uu____5946  -> get_trace_error ()
let unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____5949  -> get_unthrottle_inductives ()
let unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____5952  -> get_unsafe_tactic_exec ()
let use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____5955  -> get_use_eq_at_higher_order ()
let use_hints: Prims.unit -> Prims.bool = fun uu____5958  -> get_use_hints ()
let use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____5961  -> get_use_hint_hashes ()
let use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5966  -> get_use_native_tactics ()
let use_tactics: Prims.unit -> Prims.bool =
  fun uu____5969  -> get_use_tactics ()
let using_facts_from:
  Prims.unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5978  ->
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if FStar_Util.starts_with s "-"
        then
          (let path =
             let uu____6007 =
               FStar_Util.substring_from s (Prims.parse_int "1") in
             FStar_Ident.path_of_text uu____6007 in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s in
           ((FStar_Ident.path_of_text s1), true)) in
    let parse_setting s =
      FStar_All.pipe_right (FStar_Util.split s " ")
        (FStar_List.map parse_one_setting) in
    let uu____6043 = get_using_facts_from () in
    match uu____6043 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns ->
        let uu____6075 = FStar_List.collect parse_setting ns in
        FStar_All.pipe_right uu____6075 FStar_List.rev
let warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____6114  -> get_warn_default_effects ()
let z3_exe: Prims.unit -> Prims.string =
  fun uu____6117  ->
    let uu____6118 = get_smt () in
    match uu____6118 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let z3_cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____6126  -> get_z3cliopt ()
let z3_refresh: Prims.unit -> Prims.bool =
  fun uu____6129  -> get_z3refresh ()
let z3_rlimit: Prims.unit -> Prims.int = fun uu____6132  -> get_z3rlimit ()
let z3_rlimit_factor: Prims.unit -> Prims.int =
  fun uu____6135  -> get_z3rlimit_factor ()
let z3_seed: Prims.unit -> Prims.int = fun uu____6138  -> get_z3seed ()
let use_two_phase_tc: Prims.unit -> Prims.bool =
  fun uu____6141  -> get_use_two_phase_tc ()
let no_positivity: Prims.unit -> Prims.bool =
  fun uu____6144  -> get_no_positivity ()
let ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____6147  -> get_ml_no_eta_expand_coertions ()
let should_extract_namespace: Prims.string -> Prims.bool =
  fun m  ->
    let uu____6151 = get_extract_namespace () in
    match uu____6151 with
    | [] -> false
    | ns ->
        FStar_All.pipe_right ns
          (FStar_Util.for_some
             (fun n1  -> FStar_Util.starts_with m (FStar_String.lowercase n1)))
let should_extract_module: Prims.string -> Prims.bool =
  fun m  ->
    let uu____6164 = get_extract_module () in
    match uu____6164 with
    | [] -> false
    | l ->
        FStar_All.pipe_right l
          (FStar_Util.for_some (fun n1  -> (FStar_String.lowercase n1) = m))
let should_extract: Prims.string -> Prims.bool =
  fun m  ->
    let m1 = FStar_String.lowercase m in
    (let uu____6180 = no_extract m1 in Prims.op_Negation uu____6180) &&
      (let uu____6182 =
         let uu____6191 = get_extract_namespace () in
         let uu____6194 = get_extract_module () in (uu____6191, uu____6194) in
       match uu____6182 with
       | ([],[]) -> true
       | uu____6205 ->
           (should_extract_namespace m1) || (should_extract_module m1))
let codegen_fsharp: Prims.unit -> Prims.bool =
  fun uu____6216  ->
    let uu____6217 = codegen () in
    uu____6217 = (FStar_Pervasives_Native.Some "FSharp")