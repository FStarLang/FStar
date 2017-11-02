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
  fun uu___65_309  ->
    match uu___65_309 with
    | Bool b -> b
    | uu____311 -> failwith "Impos: expected Bool"
let as_int: option_val -> Prims.int =
  fun uu___66_314  ->
    match uu___66_314 with
    | Int b -> b
    | uu____316 -> failwith "Impos: expected Int"
let as_string: option_val -> Prims.string =
  fun uu___67_319  ->
    match uu___67_319 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____322 -> failwith "Impos: expected String"
let as_list': option_val -> option_val Prims.list =
  fun uu___68_327  ->
    match uu___68_327 with
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
    fun uu___69_378  ->
      match uu___69_378 with
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
  ("__no_positivity", (Bool false));
  ("__ml_no_eta_expand_coertions", (Bool false))]
let init: Prims.unit -> Prims.unit =
  fun uu____1305  ->
    let o = peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let clear: Prims.unit -> Prims.unit =
  fun uu____1320  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50") in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
let _run: Prims.unit = clear ()
let get_option: Prims.string -> option_val =
  fun s  ->
    let uu____1433 =
      let uu____1436 = peek () in FStar_Util.smap_try_find uu____1436 s in
    match uu____1433 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
let lookup_opt:
  'Auu____1443 . Prims.string -> (option_val -> 'Auu____1443) -> 'Auu____1443
  = fun s  -> fun c  -> c (get_option s)
let get_admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____1459  -> lookup_opt "admit_smt_queries" as_bool
let get_admit_except:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1464  -> lookup_opt "admit_except" (as_option as_string)
let get_cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____1469  -> lookup_opt "cache_checked_modules" as_bool
let get_codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1474  -> lookup_opt "codegen" (as_option as_string)
let get_codegen_lib: Prims.unit -> Prims.string Prims.list =
  fun uu____1481  -> lookup_opt "codegen-lib" (as_list as_string)
let get_debug: Prims.unit -> Prims.string Prims.list =
  fun uu____1488  -> lookup_opt "debug" (as_list as_string)
let get_debug_level: Prims.unit -> Prims.string Prims.list =
  fun uu____1495  -> lookup_opt "debug_level" (as_list as_string)
let get_dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1502  -> lookup_opt "dep" (as_option as_string)
let get_detail_errors: Prims.unit -> Prims.bool =
  fun uu____1507  -> lookup_opt "detail_errors" as_bool
let get_detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____1510  -> lookup_opt "detail_hint_replay" as_bool
let get_doc: Prims.unit -> Prims.bool =
  fun uu____1513  -> lookup_opt "doc" as_bool
let get_dump_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1518  -> lookup_opt "dump_module" (as_list as_string)
let get_eager_inference: Prims.unit -> Prims.bool =
  fun uu____1523  -> lookup_opt "eager_inference" as_bool
let get_expose_interfaces: Prims.unit -> Prims.bool =
  fun uu____1526  -> lookup_opt "expose_interfaces" as_bool
let get_extract_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1531  -> lookup_opt "extract_module" (as_list as_string)
let get_extract_namespace: Prims.unit -> Prims.string Prims.list =
  fun uu____1538  -> lookup_opt "extract_namespace" (as_list as_string)
let get_fs_typ_app: Prims.unit -> Prims.bool =
  fun uu____1543  -> lookup_opt "fs_typ_app" as_bool
let get_fstar_home: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1548  -> lookup_opt "fstar_home" (as_option as_string)
let get_gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1555  -> lookup_opt "gen_native_tactics" (as_option as_string)
let get_hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____1560  -> lookup_opt "hide_uvar_nums" as_bool
let get_hint_info: Prims.unit -> Prims.bool =
  fun uu____1563  -> lookup_opt "hint_info" as_bool
let get_hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1568  -> lookup_opt "hint_file" (as_option as_string)
let get_in: Prims.unit -> Prims.bool =
  fun uu____1573  -> lookup_opt "in" as_bool
let get_ide: Prims.unit -> Prims.bool =
  fun uu____1576  -> lookup_opt "ide" as_bool
let get_include: Prims.unit -> Prims.string Prims.list =
  fun uu____1581  -> lookup_opt "include" (as_list as_string)
let get_indent: Prims.unit -> Prims.bool =
  fun uu____1586  -> lookup_opt "indent" as_bool
let get_initial_fuel: Prims.unit -> Prims.int =
  fun uu____1589  -> lookup_opt "initial_fuel" as_int
let get_initial_ifuel: Prims.unit -> Prims.int =
  fun uu____1592  -> lookup_opt "initial_ifuel" as_int
let get_lax: Prims.unit -> Prims.bool =
  fun uu____1595  -> lookup_opt "lax" as_bool
let get_load: Prims.unit -> Prims.string Prims.list =
  fun uu____1600  -> lookup_opt "load" (as_list as_string)
let get_log_queries: Prims.unit -> Prims.bool =
  fun uu____1605  -> lookup_opt "log_queries" as_bool
let get_log_types: Prims.unit -> Prims.bool =
  fun uu____1608  -> lookup_opt "log_types" as_bool
let get_max_fuel: Prims.unit -> Prims.int =
  fun uu____1611  -> lookup_opt "max_fuel" as_int
let get_max_ifuel: Prims.unit -> Prims.int =
  fun uu____1614  -> lookup_opt "max_ifuel" as_int
let get_min_fuel: Prims.unit -> Prims.int =
  fun uu____1617  -> lookup_opt "min_fuel" as_int
let get_MLish: Prims.unit -> Prims.bool =
  fun uu____1620  -> lookup_opt "MLish" as_bool
let get_n_cores: Prims.unit -> Prims.int =
  fun uu____1623  -> lookup_opt "n_cores" as_int
let get_no_default_includes: Prims.unit -> Prims.bool =
  fun uu____1626  -> lookup_opt "no_default_includes" as_bool
let get_no_extract: Prims.unit -> Prims.string Prims.list =
  fun uu____1631  -> lookup_opt "no_extract" (as_list as_string)
let get_no_location_info: Prims.unit -> Prims.bool =
  fun uu____1636  -> lookup_opt "no_location_info" as_bool
let get_odir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1641  -> lookup_opt "odir" (as_option as_string)
let get_ugly: Prims.unit -> Prims.bool =
  fun uu____1646  -> lookup_opt "ugly" as_bool
let get_prims: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1651  -> lookup_opt "prims" (as_option as_string)
let get_print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____1656  -> lookup_opt "print_bound_var_types" as_bool
let get_print_effect_args: Prims.unit -> Prims.bool =
  fun uu____1659  -> lookup_opt "print_effect_args" as_bool
let get_print_full_names: Prims.unit -> Prims.bool =
  fun uu____1662  -> lookup_opt "print_full_names" as_bool
let get_print_implicits: Prims.unit -> Prims.bool =
  fun uu____1665  -> lookup_opt "print_implicits" as_bool
let get_print_universes: Prims.unit -> Prims.bool =
  fun uu____1668  -> lookup_opt "print_universes" as_bool
let get_print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____1671  -> lookup_opt "print_z3_statistics" as_bool
let get_prn: Prims.unit -> Prims.bool =
  fun uu____1674  -> lookup_opt "prn" as_bool
let get_query_stats: Prims.unit -> Prims.bool =
  fun uu____1677  -> lookup_opt "query_stats" as_bool
let get_record_hints: Prims.unit -> Prims.bool =
  fun uu____1680  -> lookup_opt "record_hints" as_bool
let get_reuse_hint_for:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1685  -> lookup_opt "reuse_hint_for" (as_option as_string)
let get_silent: Prims.unit -> Prims.bool =
  fun uu____1690  -> lookup_opt "silent" as_bool
let get_smt: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1695  -> lookup_opt "smt" (as_option as_string)
let get_smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____1700  -> lookup_opt "smtencoding.elim_box" as_bool
let get_smtencoding_nl_arith_repr: Prims.unit -> Prims.string =
  fun uu____1703  -> lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr: Prims.unit -> Prims.string =
  fun uu____1706  -> lookup_opt "smtencoding.l_arith_repr" as_string
let get_split_cases: Prims.unit -> Prims.int =
  fun uu____1709  -> lookup_opt "split_cases" as_int
let get_tactic_trace: Prims.unit -> Prims.bool =
  fun uu____1712  -> lookup_opt "tactic_trace" as_bool
let get_tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____1715  -> lookup_opt "tactic_trace_d" as_int
let get_timing: Prims.unit -> Prims.bool =
  fun uu____1718  -> lookup_opt "timing" as_bool
let get_trace_error: Prims.unit -> Prims.bool =
  fun uu____1721  -> lookup_opt "trace_error" as_bool
let get_unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____1724  -> lookup_opt "unthrottle_inductives" as_bool
let get_unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____1727  -> lookup_opt "unsafe_tactic_exec" as_bool
let get_use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____1730  -> lookup_opt "use_eq_at_higher_order" as_bool
let get_use_hints: Prims.unit -> Prims.bool =
  fun uu____1733  -> lookup_opt "use_hints" as_bool
let get_use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____1736  -> lookup_opt "use_hint_hashes" as_bool
let get_use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1741  -> lookup_opt "use_native_tactics" (as_option as_string)
let get_use_tactics: Prims.unit -> Prims.bool =
  fun uu____1746  ->
    let uu____1747 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____1747
let get_using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1754  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let get_verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1765  -> lookup_opt "verify_module" (as_list as_string)
let get___temp_no_proj: Prims.unit -> Prims.string Prims.list =
  fun uu____1772  -> lookup_opt "__temp_no_proj" (as_list as_string)
let get_version: Prims.unit -> Prims.bool =
  fun uu____1777  -> lookup_opt "version" as_bool
let get_warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____1780  -> lookup_opt "warn_default_effects" as_bool
let get_z3cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____1785  -> lookup_opt "z3cliopt" (as_list as_string)
let get_z3refresh: Prims.unit -> Prims.bool =
  fun uu____1790  -> lookup_opt "z3refresh" as_bool
let get_z3rlimit: Prims.unit -> Prims.int =
  fun uu____1793  -> lookup_opt "z3rlimit" as_int
let get_z3rlimit_factor: Prims.unit -> Prims.int =
  fun uu____1796  -> lookup_opt "z3rlimit_factor" as_int
let get_z3seed: Prims.unit -> Prims.int =
  fun uu____1799  -> lookup_opt "z3seed" as_int
let get_no_positivity: Prims.unit -> Prims.bool =
  fun uu____1802  -> lookup_opt "__no_positivity" as_bool
let get_ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____1805  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool
let dlevel: Prims.string -> debug_level_t =
  fun uu___70_1808  ->
    match uu___70_1808 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let one_debug_level_geq: debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1816 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let debug_level_geq: debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____1820 = get_debug_level () in
    FStar_All.pipe_right uu____1820
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
let universe_include_path_base_dirs: Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"]
let _version: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _platform: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _compiler: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _date: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _commit: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let display_version: Prims.unit -> Prims.unit =
  fun uu____1911  ->
    let uu____1912 =
      let uu____1913 = FStar_ST.op_Bang _version in
      let uu____1960 = FStar_ST.op_Bang _platform in
      let uu____2007 = FStar_ST.op_Bang _compiler in
      let uu____2054 = FStar_ST.op_Bang _date in
      let uu____2101 = FStar_ST.op_Bang _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1913
        uu____1960 uu____2007 uu____2054 uu____2101 in
    FStar_Util.print_string uu____1912
let display_usage_aux:
  'Auu____2151 'Auu____2152 .
    ('Auu____2152,Prims.string,'Auu____2151 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2199  ->
         match uu____2199 with
         | (uu____2210,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2221 =
                      let uu____2222 = FStar_Util.colorize_bold flag in
                      FStar_Util.format1 "  --%s\n" uu____2222 in
                    FStar_Util.print_string uu____2221
                  else
                    (let uu____2224 =
                       let uu____2225 = FStar_Util.colorize_bold flag in
                       FStar_Util.format2 "  --%s  %s\n" uu____2225 doc in
                     FStar_Util.print_string uu____2224)
              | FStar_Getopt.OneArg (uu____2226,argname) ->
                  if doc = ""
                  then
                    let uu____2232 =
                      let uu____2233 = FStar_Util.colorize_bold flag in
                      let uu____2234 = FStar_Util.colorize_bold argname in
                      FStar_Util.format2 "  --%s %s\n" uu____2233 uu____2234 in
                    FStar_Util.print_string uu____2232
                  else
                    (let uu____2236 =
                       let uu____2237 = FStar_Util.colorize_bold flag in
                       let uu____2238 = FStar_Util.colorize_bold argname in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2237
                         uu____2238 doc in
                     FStar_Util.print_string uu____2236))) specs
let mk_spec:
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____2262 = o in
    match uu____2262 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2292 =
                let uu____2293 = f () in set_option name uu____2293 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2304 = f x in set_option name uu____2304 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2318 = lookup_opt name (as_option as_list') in
        FStar_Util.dflt [] uu____2318 in
      mk_list (value :: prev_values)
let reverse_accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let uu____2337 =
        let uu____2340 = lookup_opt name as_list' in
        FStar_List.append uu____2340 [value] in
      mk_list uu____2337
let accumulate_string:
  'Auu____2349 .
    Prims.string ->
      ('Auu____2349 -> Prims.string) -> 'Auu____2349 -> Prims.unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2367 =
          let uu____2368 =
            let uu____2369 = post_processor value in mk_string uu____2369 in
          accumulated_option name uu____2368 in
        set_option name uu____2367
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
    match projectee with | Const _0 -> true | uu____2447 -> false
let __proj__Const__item___0: opt_type -> option_val =
  fun projectee  -> match projectee with | Const _0 -> _0
let uu___is_IntStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2459 -> false
let __proj__IntStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | IntStr _0 -> _0
let uu___is_BoolStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2470 -> false
let uu___is_PathStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2475 -> false
let __proj__PathStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | PathStr _0 -> _0
let uu___is_SimpleStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2487 -> false
let __proj__SimpleStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0
let uu___is_EnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2501 -> false
let __proj__EnumStr__item___0: opt_type -> Prims.string Prims.list =
  fun projectee  -> match projectee with | EnumStr _0 -> _0
let uu___is_OpenEnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2525 -> false
let __proj__OpenEnumStr__item___0:
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0
let uu___is_PostProcessed: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2561 -> false
let __proj__PostProcessed__item___0:
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0
let uu___is_Accumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2591 -> false
let __proj__Accumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | Accumulated _0 -> _0
let uu___is_ReverseAccumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2603 -> false
let __proj__ReverseAccumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0
let uu___is_WithSideEffect: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2621 -> false
let __proj__WithSideEffect__item___0:
  opt_type ->
    (Prims.unit -> Prims.unit,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | WithSideEffect _0 -> _0
exception InvalidArgument of Prims.string
let uu___is_InvalidArgument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2653 -> true
    | uu____2654 -> false
let __proj__InvalidArgument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2661 -> uu____2661
let rec parse_opt_val: Prims.string -> opt_type -> Prims.string -> option_val
  =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2675 ->
              let uu____2676 = FStar_Util.safe_int_of_string str_val in
              (match uu____2676 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2680 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name) in
              mk_bool uu____2680
          | PathStr uu____2683 -> mk_path str_val
          | SimpleStr uu____2684 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2689 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2702 = parse_opt_val opt_name elem_spec str_val in
              pp uu____2702
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
            let uu____2719 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1 in
            failwith uu____2719
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
    | PostProcessed (uu____2752,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2760,elem_spec) -> desc_of_opt_type elem_spec
let rec arg_spec_of_opt_type:
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ in
      let uu____2779 = desc_of_opt_type typ in
      match uu____2779 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2785  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
let pp_validate_dir: option_val -> option_val =
  fun p  -> let pp = as_string p in FStar_Util.mkdir false pp; p
let pp_lowercase: option_val -> option_val =
  fun s  ->
    let uu____2797 =
      let uu____2798 = as_string s in FStar_String.lowercase uu____2798 in
    mk_string uu____2797
let rec specs_with_types:
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun uu____2815  ->
    let uu____2826 =
      let uu____2837 =
        let uu____2848 =
          let uu____2857 = let uu____2858 = mk_bool true in Const uu____2858 in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2857,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying") in
        let uu____2859 =
          let uu____2870 =
            let uu____2881 =
              let uu____2892 =
                let uu____2903 =
                  let uu____2914 =
                    let uu____2925 =
                      let uu____2934 =
                        let uu____2935 = mk_bool true in Const uu____2935 in
                      (FStar_Getopt.noshort, "detail_errors", uu____2934,
                        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1") in
                    let uu____2936 =
                      let uu____2947 =
                        let uu____2956 =
                          let uu____2957 = mk_bool true in Const uu____2957 in
                        (FStar_Getopt.noshort, "detail_hint_replay",
                          uu____2956,
                          "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1") in
                      let uu____2958 =
                        let uu____2969 =
                          let uu____2978 =
                            let uu____2979 = mk_bool true in Const uu____2979 in
                          (FStar_Getopt.noshort, "doc", uu____2978,
                            "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.") in
                        let uu____2980 =
                          let uu____2991 =
                            let uu____3002 =
                              let uu____3011 =
                                let uu____3012 = mk_bool true in
                                Const uu____3012 in
                              (FStar_Getopt.noshort, "eager_inference",
                                uu____3011,
                                "Solve all type-inference constraints eagerly; more efficient but at the cost of generality") in
                            let uu____3013 =
                              let uu____3024 =
                                let uu____3035 =
                                  let uu____3046 =
                                    let uu____3055 =
                                      let uu____3056 = mk_bool true in
                                      Const uu____3056 in
                                    (FStar_Getopt.noshort,
                                      "expose_interfaces", uu____3055,
                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)") in
                                  let uu____3057 =
                                    let uu____3068 =
                                      let uu____3079 =
                                        let uu____3090 =
                                          let uu____3099 =
                                            let uu____3100 = mk_bool true in
                                            Const uu____3100 in
                                          (FStar_Getopt.noshort,
                                            "hide_uvar_nums", uu____3099,
                                            "Don't print unification variable numbers") in
                                        let uu____3101 =
                                          let uu____3112 =
                                            let uu____3123 =
                                              let uu____3132 =
                                                let uu____3133 = mk_bool true in
                                                Const uu____3133 in
                                              (FStar_Getopt.noshort,
                                                "hint_info", uu____3132,
                                                "Print information regarding hints (deprecated; use --query_stats instead)") in
                                            let uu____3134 =
                                              let uu____3145 =
                                                let uu____3154 =
                                                  let uu____3155 =
                                                    mk_bool true in
                                                  Const uu____3155 in
                                                (FStar_Getopt.noshort, "in",
                                                  uu____3154,
                                                  "Legacy interactive mode; reads input from stdin") in
                                              let uu____3156 =
                                                let uu____3167 =
                                                  let uu____3176 =
                                                    let uu____3177 =
                                                      mk_bool true in
                                                    Const uu____3177 in
                                                  (FStar_Getopt.noshort,
                                                    "ide", uu____3176,
                                                    "JSON-based interactive mode for IDEs") in
                                                let uu____3178 =
                                                  let uu____3189 =
                                                    let uu____3200 =
                                                      let uu____3209 =
                                                        let uu____3210 =
                                                          mk_bool true in
                                                        Const uu____3210 in
                                                      (FStar_Getopt.noshort,
                                                        "indent", uu____3209,
                                                        "Parses and outputs the files on the command line") in
                                                    let uu____3211 =
                                                      let uu____3222 =
                                                        let uu____3233 =
                                                          let uu____3244 =
                                                            let uu____3253 =
                                                              let uu____3254
                                                                =
                                                                mk_bool true in
                                                              Const
                                                                uu____3254 in
                                                            (FStar_Getopt.noshort,
                                                              "lax",
                                                              uu____3253,
                                                              "Run the lax-type checker only (admit all verification conditions)") in
                                                          let uu____3255 =
                                                            let uu____3266 =
                                                              let uu____3277
                                                                =
                                                                let uu____3286
                                                                  =
                                                                  let uu____3287
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                  Const
                                                                    uu____3287 in
                                                                (FStar_Getopt.noshort,
                                                                  "log_types",
                                                                  uu____3286,
                                                                  "Print types computed for data/val/let-bindings") in
                                                              let uu____3288
                                                                =
                                                                let uu____3299
                                                                  =
                                                                  let uu____3308
                                                                    =
                                                                    let uu____3309
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3309 in
                                                                  (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3308,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go") in
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
                                                                    "MLish",
                                                                    uu____3363,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)") in
                                                                    let uu____3365
                                                                    =
                                                                    let uu____3376
                                                                    =
                                                                    let uu____3387
                                                                    =
                                                                    let uu____3396
                                                                    =
                                                                    let uu____3397
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3397 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3396,
                                                                    "Ignore the default module search paths") in
                                                                    let uu____3398
                                                                    =
                                                                    let uu____3409
                                                                    =
                                                                    let uu____3420
                                                                    =
                                                                    let uu____3429
                                                                    =
                                                                    let uu____3430
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3430 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3429,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)") in
                                                                    let uu____3431
                                                                    =
                                                                    let uu____3442
                                                                    =
                                                                    let uu____3453
                                                                    =
                                                                    let uu____3464
                                                                    =
                                                                    let uu____3473
                                                                    =
                                                                    let uu____3474
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3474 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3473,
                                                                    "Print the types of bound variables") in
                                                                    let uu____3475
                                                                    =
                                                                    let uu____3486
                                                                    =
                                                                    let uu____3495
                                                                    =
                                                                    let uu____3496
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3496 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3495,
                                                                    "Print inferred predicate transformers for all computation types") in
                                                                    let uu____3497
                                                                    =
                                                                    let uu____3508
                                                                    =
                                                                    let uu____3517
                                                                    =
                                                                    let uu____3518
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3518 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3517,
                                                                    "Print full names of variables") in
                                                                    let uu____3519
                                                                    =
                                                                    let uu____3530
                                                                    =
                                                                    let uu____3539
                                                                    =
                                                                    let uu____3540
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3540 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3539,
                                                                    "Print implicit arguments") in
                                                                    let uu____3541
                                                                    =
                                                                    let uu____3552
                                                                    =
                                                                    let uu____3561
                                                                    =
                                                                    let uu____3562
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3562 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3561,
                                                                    "Print universes") in
                                                                    let uu____3563
                                                                    =
                                                                    let uu____3574
                                                                    =
                                                                    let uu____3583
                                                                    =
                                                                    let uu____3584
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3584 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3583,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)") in
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
                                                                    "prn",
                                                                    uu____3605,
                                                                    "Print full names (deprecated; use --print_full_names instead)") in
                                                                    let uu____3607
                                                                    =
                                                                    let uu____3618
                                                                    =
                                                                    let uu____3627
                                                                    =
                                                                    let uu____3628
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3628 in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3627,
                                                                    "Print SMT query statistics") in
                                                                    let uu____3629
                                                                    =
                                                                    let uu____3640
                                                                    =
                                                                    let uu____3649
                                                                    =
                                                                    let uu____3650
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3650 in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3649,
                                                                    "Record a database of hints for efficient proof replay") in
                                                                    let uu____3651
                                                                    =
                                                                    let uu____3662
                                                                    =
                                                                    let uu____3673
                                                                    =
                                                                    let uu____3682
                                                                    =
                                                                    let uu____3683
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3683 in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3682,
                                                                    " ") in
                                                                    let uu____3684
                                                                    =
                                                                    let uu____3695
                                                                    =
                                                                    let uu____3706
                                                                    =
                                                                    let uu____3717
                                                                    =
                                                                    let uu____3728
                                                                    =
                                                                    let uu____3739
                                                                    =
                                                                    let uu____3750
                                                                    =
                                                                    let uu____3759
                                                                    =
                                                                    let uu____3760
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3760 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3759,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)") in
                                                                    let uu____3761
                                                                    =
                                                                    let uu____3772
                                                                    =
                                                                    let uu____3783
                                                                    =
                                                                    let uu____3792
                                                                    =
                                                                    let uu____3793
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3793 in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3792,
                                                                    "Print the time it takes to verify each top-level definition") in
                                                                    let uu____3794
                                                                    =
                                                                    let uu____3805
                                                                    =
                                                                    let uu____3814
                                                                    =
                                                                    let uu____3815
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3815 in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3814,
                                                                    "Don't print an error message; show an exception trace instead") in
                                                                    let uu____3816
                                                                    =
                                                                    let uu____3827
                                                                    =
                                                                    let uu____3836
                                                                    =
                                                                    let uu____3837
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3837 in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3836,
                                                                    "Emit output formatted for debugging") in
                                                                    let uu____3838
                                                                    =
                                                                    let uu____3849
                                                                    =
                                                                    let uu____3858
                                                                    =
                                                                    let uu____3859
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3859 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____3858,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)") in
                                                                    let uu____3860
                                                                    =
                                                                    let uu____3871
                                                                    =
                                                                    let uu____3880
                                                                    =
                                                                    let uu____3881
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3881 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____3880,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.") in
                                                                    let uu____3882
                                                                    =
                                                                    let uu____3893
                                                                    =
                                                                    let uu____3902
                                                                    =
                                                                    let uu____3903
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3903 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____3902,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)") in
                                                                    let uu____3904
                                                                    =
                                                                    let uu____3915
                                                                    =
                                                                    let uu____3924
                                                                    =
                                                                    let uu____3925
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3925 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____3924,
                                                                    "Use a previously recorded hints database for proof replay") in
                                                                    let uu____3926
                                                                    =
                                                                    let uu____3937
                                                                    =
                                                                    let uu____3946
                                                                    =
                                                                    let uu____3947
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3947 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____3946,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database") in
                                                                    let uu____3948
                                                                    =
                                                                    let uu____3959
                                                                    =
                                                                    let uu____3970
                                                                    =
                                                                    let uu____3979
                                                                    =
                                                                    let uu____3980
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3980 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____3979,
                                                                    "Do not run the tactic engine before discharging a VC") in
                                                                    let uu____3981
                                                                    =
                                                                    let uu____3992
                                                                    =
                                                                    let uu____4003
                                                                    =
                                                                    let uu____4014
                                                                    =
                                                                    let uu____4023
                                                                    =
                                                                    let uu____4024
                                                                    =
                                                                    let uu____4031
                                                                    =
                                                                    let uu____4032
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4032 in
                                                                    ((fun
                                                                    uu____4037
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____4031) in
                                                                    WithSideEffect
                                                                    uu____4024 in
                                                                    (118,
                                                                    "version",
                                                                    uu____4023,
                                                                    "Display version number") in
                                                                    let uu____4039
                                                                    =
                                                                    let uu____4050
                                                                    =
                                                                    let uu____4059
                                                                    =
                                                                    let uu____4060
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4060 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4059,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)") in
                                                                    let uu____4061
                                                                    =
                                                                    let uu____4072
                                                                    =
                                                                    let uu____4083
                                                                    =
                                                                    let uu____4092
                                                                    =
                                                                    let uu____4093
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4093 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4092,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness") in
                                                                    let uu____4094
                                                                    =
                                                                    let uu____4105
                                                                    =
                                                                    let uu____4116
                                                                    =
                                                                    let uu____4127
                                                                    =
                                                                    let uu____4138
                                                                    =
                                                                    let uu____4147
                                                                    =
                                                                    let uu____4148
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4148 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4147,
                                                                    "Don't check positivity of inductive types") in
                                                                    let uu____4149
                                                                    =
                                                                    let uu____4160
                                                                    =
                                                                    let uu____4169
                                                                    =
                                                                    let uu____4170
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4170 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4169,
                                                                    "Do not eta-expand coertions in generated OCaml") in
                                                                    let uu____4171
                                                                    =
                                                                    let uu____4182
                                                                    =
                                                                    let uu____4191
                                                                    =
                                                                    let uu____4192
                                                                    =
                                                                    let uu____4199
                                                                    =
                                                                    let uu____4200
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4200 in
                                                                    ((fun
                                                                    uu____4205
                                                                     ->
                                                                    (
                                                                    let uu____4207
                                                                    =
                                                                    specs () in
                                                                    display_usage_aux
                                                                    uu____4207);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____4199) in
                                                                    WithSideEffect
                                                                    uu____4192 in
                                                                    (104,
                                                                    "help",
                                                                    uu____4191,
                                                                    "Display this information") in
                                                                    [uu____4182] in
                                                                    uu____4160
                                                                    ::
                                                                    uu____4171 in
                                                                    uu____4138
                                                                    ::
                                                                    uu____4149 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4127 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4116 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4105 in
                                                                    uu____4083
                                                                    ::
                                                                    uu____4094 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4072 in
                                                                    uu____4050
                                                                    ::
                                                                    uu____4061 in
                                                                    uu____4014
                                                                    ::
                                                                    uu____4039 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4003 in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____3992 in
                                                                    uu____3970
                                                                    ::
                                                                    uu____3981 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____3959 in
                                                                    uu____3937
                                                                    ::
                                                                    uu____3948 in
                                                                    uu____3915
                                                                    ::
                                                                    uu____3926 in
                                                                    uu____3893
                                                                    ::
                                                                    uu____3904 in
                                                                    uu____3871
                                                                    ::
                                                                    uu____3882 in
                                                                    uu____3849
                                                                    ::
                                                                    uu____3860 in
                                                                    uu____3827
                                                                    ::
                                                                    uu____3838 in
                                                                    uu____3805
                                                                    ::
                                                                    uu____3816 in
                                                                    uu____3783
                                                                    ::
                                                                    uu____3794 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3772 in
                                                                    uu____3750
                                                                    ::
                                                                    uu____3761 in
                                                                    (FStar_Getopt.noshort,
                                                                    "split_cases",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Partition VC of a match into groups of <positive_integer> cases")
                                                                    ::
                                                                    uu____3739 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3728 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3717 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3706 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3695 in
                                                                    uu____3673
                                                                    ::
                                                                    uu____3684 in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3662 in
                                                                    uu____3640
                                                                    ::
                                                                    uu____3651 in
                                                                    uu____3618
                                                                    ::
                                                                    uu____3629 in
                                                                    uu____3596
                                                                    ::
                                                                    uu____3607 in
                                                                    uu____3574
                                                                    ::
                                                                    uu____3585 in
                                                                    uu____3552
                                                                    ::
                                                                    uu____3563 in
                                                                    uu____3530
                                                                    ::
                                                                    uu____3541 in
                                                                    uu____3508
                                                                    ::
                                                                    uu____3519 in
                                                                    uu____3486
                                                                    ::
                                                                    uu____3497 in
                                                                    uu____3464
                                                                    ::
                                                                    uu____3475 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3453 in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3442 in
                                                                    uu____3420
                                                                    ::
                                                                    uu____3431 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Do not extract code from this module")
                                                                    ::
                                                                    uu____3409 in
                                                                    uu____3387
                                                                    ::
                                                                    uu____3398 in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3376 in
                                                                    uu____3354
                                                                    ::
                                                                    uu____3365 in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3343 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3332 in
                                                                  (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (
                                                                    IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3321 in
                                                                uu____3299 ::
                                                                  uu____3310 in
                                                              uu____3277 ::
                                                                uu____3288 in
                                                            (FStar_Getopt.noshort,
                                                              "load",
                                                              (ReverseAccumulated
                                                                 (PathStr
                                                                    "module")),
                                                              "Load compiled module")
                                                              :: uu____3266 in
                                                          uu____3244 ::
                                                            uu____3255 in
                                                        (FStar_Getopt.noshort,
                                                          "initial_ifuel",
                                                          (IntStr
                                                             "non-negative integer"),
                                                          "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                          :: uu____3233 in
                                                      (FStar_Getopt.noshort,
                                                        "initial_fuel",
                                                        (IntStr
                                                           "non-negative integer"),
                                                        "Number of unrolling of recursive functions to try initially (default 2)")
                                                        :: uu____3222 in
                                                    uu____3200 :: uu____3211 in
                                                  (FStar_Getopt.noshort,
                                                    "include",
                                                    (ReverseAccumulated
                                                       (PathStr "path")),
                                                    "A directory in which to search for files included on the command line")
                                                    :: uu____3189 in
                                                uu____3167 :: uu____3178 in
                                              uu____3145 :: uu____3156 in
                                            uu____3123 :: uu____3134 in
                                          (FStar_Getopt.noshort, "hint_file",
                                            (PathStr "path"),
                                            "Read/write hints to <path> (instead of module-specific hints files)")
                                            :: uu____3112 in
                                        uu____3090 :: uu____3101 in
                                      (FStar_Getopt.noshort,
                                        "gen_native_tactics",
                                        (PathStr "[path]"),
                                        "Compile all user tactics used in the module in <path>")
                                        :: uu____3079 in
                                    (FStar_Getopt.noshort, "fstar_home",
                                      (PathStr "dir"),
                                      "Set the FSTAR_HOME variable to <dir>")
                                      :: uu____3068 in
                                  uu____3046 :: uu____3057 in
                                (FStar_Getopt.noshort, "extract_namespace",
                                  (Accumulated
                                     (PostProcessed
                                        (pp_lowercase,
                                          (SimpleStr "namespace name")))),
                                  "Only extract modules in the specified namespace")
                                  :: uu____3035 in
                              (FStar_Getopt.noshort, "extract_module",
                                (Accumulated
                                   (PostProcessed
                                      (pp_lowercase,
                                        (SimpleStr "module_name")))),
                                "Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                :: uu____3024 in
                            uu____3002 :: uu____3013 in
                          (FStar_Getopt.noshort, "dump_module",
                            (Accumulated (SimpleStr "module_name")), "") ::
                            uu____2991 in
                        uu____2969 :: uu____2980 in
                      uu____2947 :: uu____2958 in
                    uu____2925 :: uu____2936 in
                  (FStar_Getopt.noshort, "dep",
                    (EnumStr ["make"; "graph"; "full"]),
                    "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                    :: uu____2914 in
                (FStar_Getopt.noshort, "debug_level",
                  (Accumulated
                     (OpenEnumStr
                        (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                  "Control the verbosity of debugging info") :: uu____2903 in
              (FStar_Getopt.noshort, "debug",
                (Accumulated (SimpleStr "module_name")),
                "Print lots of debugging information while checking module")
                :: uu____2892 in
            (FStar_Getopt.noshort, "codegen-lib",
              (Accumulated (SimpleStr "namespace")),
              "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
              :: uu____2881 in
          (FStar_Getopt.noshort, "codegen",
            (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "tactics"]),
            "Generate code for execution") :: uu____2870 in
        uu____2848 :: uu____2859 in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2837 in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2826
and specs: Prims.unit -> FStar_Getopt.opt Prims.list =
  fun uu____4884  ->
    let uu____4887 = specs_with_types () in
    FStar_List.map
      (fun uu____4912  ->
         match uu____4912 with
         | (short,long,typ,doc) ->
             let uu____4925 =
               let uu____4936 = arg_spec_of_opt_type long typ in
               (short, long, uu____4936, doc) in
             mk_spec uu____4925) uu____4887
let settable: Prims.string -> Prims.bool =
  fun uu___71_4943  ->
    match uu___71_4943 with
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
    | uu____4944 -> false
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
       (fun uu____5001  ->
          match uu____5001 with
          | (uu____5012,x,uu____5014,uu____5015) -> settable x))
let resettable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5061  ->
          match uu____5061 with
          | (uu____5072,x,uu____5074,uu____5075) -> resettable x))
let display_usage: Prims.unit -> Prims.unit =
  fun uu____5082  ->
    let uu____5083 = specs () in display_usage_aux uu____5083
let fstar_home: Prims.unit -> Prims.string =
  fun uu____5098  ->
    let uu____5099 = get_fstar_home () in
    match uu____5099 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        ((let uu____5105 =
            let uu____5110 = mk_string x1 in ("fstar_home", uu____5110) in
          set_option' uu____5105);
         x1)
    | FStar_Pervasives_Native.Some x -> x
exception File_argument of Prims.string
let uu___is_File_argument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____5118 -> true
    | uu____5119 -> false
let __proj__File_argument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____5126 -> uu____5126
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
          let uu____5170 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____5170
let file_list_: Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let parse_cmd_line:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____5192  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5197 =
             let uu____5200 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____5200 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____5197) in
    let uu____5303 =
      let uu____5306 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5306 in
    (res, uu____5303)
let file_list: Prims.unit -> Prims.string Prims.list =
  fun uu____5365  -> FStar_ST.op_Bang file_list_
let restore_cmd_line_options: Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____5425 = specs () in
       FStar_Getopt.parse_cmdline uu____5425 (fun x  -> ()) in
     (let uu____5431 =
        let uu____5436 =
          let uu____5437 = FStar_List.map mk_string old_verify_module in
          List uu____5437 in
        ("verify_module", uu____5436) in
      set_option' uu____5431);
     r)
let module_name_of_file_name: Prims.string -> Prims.string =
  fun f  ->
    let f1 = FStar_Util.basename f in
    let f2 =
      let uu____5445 =
        let uu____5446 =
          let uu____5447 =
            let uu____5448 = FStar_Util.get_file_extension f1 in
            FStar_String.length uu____5448 in
          (FStar_String.length f1) - uu____5447 in
        uu____5446 - (Prims.parse_int "1") in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5445 in
    FStar_String.lowercase f2
let should_verify: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5452 = get_lax () in
    if uu____5452
    then false
    else
      (let l = get_verify_module () in
       FStar_List.contains (FStar_String.lowercase m) l)
let should_verify_file: Prims.string -> Prims.bool =
  fun fn  ->
    let uu____5460 = module_name_of_file_name fn in should_verify uu____5460
let dont_gen_projectors: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5464 = get___temp_no_proj () in
    FStar_List.contains m uu____5464
let should_print_message: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5470 = should_verify m in
    if uu____5470 then m <> "Prims" else false
let include_path: Prims.unit -> Prims.string Prims.list =
  fun uu____5476  ->
    let uu____5477 = get_no_default_includes () in
    if uu____5477
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____5485 =
         let uu____5488 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____5488
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____5501 =
         let uu____5504 = get_include () in
         FStar_List.append uu____5504 ["."] in
       FStar_List.append uu____5485 uu____5501)
let find_file: Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____5512 = FStar_Util.is_path_absolute filename in
    if uu____5512
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5519 =
         let uu____5522 = include_path () in FStar_List.rev uu____5522 in
       FStar_Util.find_map uu____5519
         (fun p  ->
            let path = FStar_Util.join_paths p filename in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
let prims: Prims.unit -> Prims.string =
  fun uu____5534  ->
    let uu____5535 = get_prims () in
    match uu____5535 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst" in
        let uu____5539 = find_file filename in
        (match uu____5539 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5543 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename in
             failwith uu____5543)
    | FStar_Pervasives_Native.Some x -> x
let prims_basename: Prims.unit -> Prims.string =
  fun uu____5547  ->
    let uu____5548 = prims () in FStar_Util.basename uu____5548
let pervasives: Prims.unit -> Prims.string =
  fun uu____5551  ->
    let filename = "FStar.Pervasives.fst" in
    let uu____5553 = find_file filename in
    match uu____5553 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5557 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5557
let pervasives_basename: Prims.unit -> Prims.string =
  fun uu____5560  ->
    let uu____5561 = pervasives () in FStar_Util.basename uu____5561
let pervasives_native_basename: Prims.unit -> Prims.string =
  fun uu____5564  ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____5566 = find_file filename in
    match uu____5566 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5570 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5570
let prepend_output_dir: Prims.string -> Prims.string =
  fun fname  ->
    let uu____5574 = get_odir () in
    match uu____5574 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
let __temp_no_proj: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5581 = get___temp_no_proj () in
    FStar_All.pipe_right uu____5581 (FStar_List.contains s)
let admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____5588  -> get_admit_smt_queries ()
let admit_except: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5593  -> get_admit_except ()
let cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____5596  -> get_cache_checked_modules ()
let codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5601  -> get_codegen ()
let codegen_libs: Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____5608  ->
    let uu____5609 = get_codegen_lib () in
    FStar_All.pipe_right uu____5609
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
let debug_any: Prims.unit -> Prims.bool =
  fun uu____5624  -> let uu____5625 = get_debug () in uu____5625 <> []
let debug_at_level: Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      (let uu____5638 = get_debug () in
       FStar_All.pipe_right uu____5638 (FStar_List.contains modul)) &&
        (debug_level_geq level)
let dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5647  -> get_dep ()
let detail_errors: Prims.unit -> Prims.bool =
  fun uu____5650  -> get_detail_errors ()
let detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____5653  -> get_detail_hint_replay ()
let doc: Prims.unit -> Prims.bool = fun uu____5656  -> get_doc ()
let dump_module: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5660 = get_dump_module () in
    FStar_All.pipe_right uu____5660 (FStar_List.contains s)
let eager_inference: Prims.unit -> Prims.bool =
  fun uu____5667  -> get_eager_inference ()
let expose_interfaces: Prims.unit -> Prims.bool =
  fun uu____5670  -> get_expose_interfaces ()
let fs_typ_app: Prims.string -> Prims.bool =
  fun filename  ->
    let uu____5674 = FStar_ST.op_Bang light_off_files in
    FStar_List.contains filename uu____5674
let gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5731  -> get_gen_native_tactics ()
let full_context_dependency: Prims.unit -> Prims.bool =
  fun uu____5734  -> true
let hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____5737  -> get_hide_uvar_nums ()
let hint_info: Prims.unit -> Prims.bool =
  fun uu____5740  -> (get_hint_info ()) || (get_query_stats ())
let hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5745  -> get_hint_file ()
let ide: Prims.unit -> Prims.bool = fun uu____5748  -> get_ide ()
let indent: Prims.unit -> Prims.bool = fun uu____5751  -> get_indent ()
let initial_fuel: Prims.unit -> Prims.int =
  fun uu____5754  ->
    let uu____5755 = get_initial_fuel () in
    let uu____5756 = get_max_fuel () in Prims.min uu____5755 uu____5756
let initial_ifuel: Prims.unit -> Prims.int =
  fun uu____5759  ->
    let uu____5760 = get_initial_ifuel () in
    let uu____5761 = get_max_ifuel () in Prims.min uu____5760 uu____5761
let interactive: Prims.unit -> Prims.bool =
  fun uu____5764  -> (get_in ()) || (get_ide ())
let lax: Prims.unit -> Prims.bool = fun uu____5767  -> get_lax ()
let load: Prims.unit -> Prims.string Prims.list =
  fun uu____5772  -> get_load ()
let legacy_interactive: Prims.unit -> Prims.bool =
  fun uu____5775  -> get_in ()
let log_queries: Prims.unit -> Prims.bool =
  fun uu____5778  -> get_log_queries ()
let log_types: Prims.unit -> Prims.bool = fun uu____5781  -> get_log_types ()
let max_fuel: Prims.unit -> Prims.int = fun uu____5784  -> get_max_fuel ()
let max_ifuel: Prims.unit -> Prims.int = fun uu____5787  -> get_max_ifuel ()
let min_fuel: Prims.unit -> Prims.int = fun uu____5790  -> get_min_fuel ()
let ml_ish: Prims.unit -> Prims.bool = fun uu____5793  -> get_MLish ()
let set_ml_ish: Prims.unit -> Prims.unit =
  fun uu____5796  -> set_option "MLish" (Bool true)
let n_cores: Prims.unit -> Prims.int = fun uu____5799  -> get_n_cores ()
let no_default_includes: Prims.unit -> Prims.bool =
  fun uu____5802  -> get_no_default_includes ()
let no_extract: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5806 = get_no_extract () in
    FStar_All.pipe_right uu____5806 (FStar_List.contains s)
let no_location_info: Prims.unit -> Prims.bool =
  fun uu____5813  -> get_no_location_info ()
let output_dir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5818  -> get_odir ()
let ugly: Prims.unit -> Prims.bool = fun uu____5821  -> get_ugly ()
let print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____5824  -> get_print_bound_var_types ()
let print_effect_args: Prims.unit -> Prims.bool =
  fun uu____5827  -> get_print_effect_args ()
let print_implicits: Prims.unit -> Prims.bool =
  fun uu____5830  -> get_print_implicits ()
let print_real_names: Prims.unit -> Prims.bool =
  fun uu____5833  -> (get_prn ()) || (get_print_full_names ())
let print_universes: Prims.unit -> Prims.bool =
  fun uu____5836  -> get_print_universes ()
let print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____5839  -> (get_print_z3_statistics ()) || (get_query_stats ())
let query_stats: Prims.unit -> Prims.bool =
  fun uu____5842  -> get_query_stats ()
let record_hints: Prims.unit -> Prims.bool =
  fun uu____5845  -> get_record_hints ()
let reuse_hint_for: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____5850  -> get_reuse_hint_for ()
let silent: Prims.unit -> Prims.bool = fun uu____5853  -> get_silent ()
let smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____5856  -> get_smtencoding_elim_box ()
let smtencoding_nl_arith_native: Prims.unit -> Prims.bool =
  fun uu____5859  ->
    let uu____5860 = get_smtencoding_nl_arith_repr () in
    uu____5860 = "native"
let smtencoding_nl_arith_wrapped: Prims.unit -> Prims.bool =
  fun uu____5863  ->
    let uu____5864 = get_smtencoding_nl_arith_repr () in
    uu____5864 = "wrapped"
let smtencoding_nl_arith_default: Prims.unit -> Prims.bool =
  fun uu____5867  ->
    let uu____5868 = get_smtencoding_nl_arith_repr () in
    uu____5868 = "boxwrap"
let smtencoding_l_arith_native: Prims.unit -> Prims.bool =
  fun uu____5871  ->
    let uu____5872 = get_smtencoding_l_arith_repr () in uu____5872 = "native"
let smtencoding_l_arith_default: Prims.unit -> Prims.bool =
  fun uu____5875  ->
    let uu____5876 = get_smtencoding_l_arith_repr () in
    uu____5876 = "boxwrap"
let split_cases: Prims.unit -> Prims.int =
  fun uu____5879  -> get_split_cases ()
let tactic_trace: Prims.unit -> Prims.bool =
  fun uu____5882  -> get_tactic_trace ()
let tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____5885  -> get_tactic_trace_d ()
let timing: Prims.unit -> Prims.bool = fun uu____5888  -> get_timing ()
let trace_error: Prims.unit -> Prims.bool =
  fun uu____5891  -> get_trace_error ()
let unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____5894  -> get_unthrottle_inductives ()
let unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____5897  -> get_unsafe_tactic_exec ()
let use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____5900  -> get_use_eq_at_higher_order ()
let use_hints: Prims.unit -> Prims.bool = fun uu____5903  -> get_use_hints ()
let use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____5906  -> get_use_hint_hashes ()
let use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5911  -> get_use_native_tactics ()
let use_tactics: Prims.unit -> Prims.bool =
  fun uu____5914  -> get_use_tactics ()
let using_facts_from:
  Prims.unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5923  ->
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if FStar_Util.starts_with s "-"
        then
          (let path =
             let uu____5952 =
               FStar_Util.substring_from s (Prims.parse_int "1") in
             FStar_Ident.path_of_text uu____5952 in
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
    let uu____5988 = get_using_facts_from () in
    match uu____5988 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns ->
        let uu____6020 = FStar_List.collect parse_setting ns in
        FStar_All.pipe_right uu____6020 FStar_List.rev
let warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____6059  -> get_warn_default_effects ()
let z3_exe: Prims.unit -> Prims.string =
  fun uu____6062  ->
    let uu____6063 = get_smt () in
    match uu____6063 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let z3_cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____6071  -> get_z3cliopt ()
let z3_refresh: Prims.unit -> Prims.bool =
  fun uu____6074  -> get_z3refresh ()
let z3_rlimit: Prims.unit -> Prims.int = fun uu____6077  -> get_z3rlimit ()
let z3_rlimit_factor: Prims.unit -> Prims.int =
  fun uu____6080  -> get_z3rlimit_factor ()
let z3_seed: Prims.unit -> Prims.int = fun uu____6083  -> get_z3seed ()
let no_positivity: Prims.unit -> Prims.bool =
  fun uu____6086  -> get_no_positivity ()
let ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____6089  -> get_ml_no_eta_expand_coertions ()
let should_extract: Prims.string -> Prims.bool =
  fun m  ->
    (let uu____6095 = no_extract m in Prims.op_Negation uu____6095) &&
      (let uu____6098 = get_extract_module () in
       match uu____6098 with
       | [] ->
           let uu____6101 = get_extract_namespace () in
           (match uu____6101 with
            | [] -> true
            | ns ->
                FStar_Util.for_some
                  (FStar_Util.starts_with (FStar_String.lowercase m)) ns)
       | l -> FStar_List.contains (FStar_String.lowercase m) l)
let codegen_fsharp: Prims.unit -> Prims.bool =
  fun uu____6112  ->
    let uu____6113 = codegen () in
    uu____6113 = (FStar_Pervasives_Native.Some "FSharp")