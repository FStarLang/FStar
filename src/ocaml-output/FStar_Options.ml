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
  fun uu____213  -> FStar_ST.op_Colon_Equals __unit_tests__ true
let __clear_unit_tests: Prims.unit -> Prims.unit =
  fun uu____264  -> FStar_ST.op_Colon_Equals __unit_tests__ false
let as_bool: option_val -> Prims.bool =
  fun uu___35_315  ->
    match uu___35_315 with
    | Bool b -> b
    | uu____317 -> failwith "Impos: expected Bool"
let as_int: option_val -> Prims.int =
  fun uu___36_320  ->
    match uu___36_320 with
    | Int b -> b
    | uu____322 -> failwith "Impos: expected Int"
let as_string: option_val -> Prims.string =
  fun uu___37_325  ->
    match uu___37_325 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____328 -> failwith "Impos: expected String"
let as_list': option_val -> option_val Prims.list =
  fun uu___38_333  ->
    match uu___38_333 with
    | List ts -> ts
    | uu____339 -> failwith "Impos: expected List"
let as_list:
  'Auu____345 .
    (option_val -> 'Auu____345) -> option_val -> 'Auu____345 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____361 = as_list' x in
      FStar_All.pipe_right uu____361 (FStar_List.map as_t)
let as_option:
  'Auu____371 .
    (option_val -> 'Auu____371) ->
      option_val -> 'Auu____371 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___39_384  ->
      match uu___39_384 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____388 = as_t v1 in FStar_Pervasives_Native.Some uu____388
type optionstate = option_val FStar_Util.smap[@@deriving show]
let fstar_options: optionstate Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let peek: Prims.unit -> optionstate =
  fun uu____406  ->
    let uu____407 = FStar_ST.op_Bang fstar_options in FStar_List.hd uu____407
let pop: Prims.unit -> Prims.unit =
  fun uu____464  ->
    let uu____465 = FStar_ST.op_Bang fstar_options in
    match uu____465 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____520::[] -> failwith "TOO MANY POPS!"
    | uu____521::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
let push: Prims.unit -> Prims.unit =
  fun uu____579  ->
    let uu____580 =
      let uu____583 =
        let uu____586 = peek () in FStar_Util.smap_copy uu____586 in
      let uu____589 = FStar_ST.op_Bang fstar_options in uu____583 ::
        uu____589 in
    FStar_ST.op_Colon_Equals fstar_options uu____580
let set: optionstate -> Prims.unit =
  fun o  ->
    let uu____703 = FStar_ST.op_Bang fstar_options in
    match uu____703 with
    | [] -> failwith "set on empty option stack"
    | uu____758::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
let set_option: Prims.string -> option_val -> Prims.unit =
  fun k  ->
    fun v1  -> let uu____820 = peek () in FStar_Util.smap_add uu____820 k v1
let set_option':
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> Prims.unit =
  fun uu____829  -> match uu____829 with | (k,v1) -> set_option k v1
let with_saved_options: 'a . (Prims.unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f () in pop (); retv)
let light_off_files: Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let add_light_off_file: Prims.string -> Prims.unit =
  fun filename  ->
    let uu____867 =
      let uu____870 = FStar_ST.op_Bang light_off_files in filename ::
        uu____870 in
    FStar_ST.op_Colon_Equals light_off_files uu____867
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
  fun uu____1341  ->
    let o = peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let clear: Prims.unit -> Prims.unit =
  fun uu____1356  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50") in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
let _run: Prims.unit = clear ()
let get_option: Prims.string -> option_val =
  fun s  ->
    let uu____1473 =
      let uu____1476 = peek () in FStar_Util.smap_try_find uu____1476 s in
    match uu____1473 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
let lookup_opt:
  'Auu____1483 . Prims.string -> (option_val -> 'Auu____1483) -> 'Auu____1483
  = fun s  -> fun c  -> c (get_option s)
let get_admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____1499  -> lookup_opt "admit_smt_queries" as_bool
let get_admit_except:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1504  -> lookup_opt "admit_except" (as_option as_string)
let get_cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____1509  -> lookup_opt "cache_checked_modules" as_bool
let get_codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1514  -> lookup_opt "codegen" (as_option as_string)
let get_codegen_lib: Prims.unit -> Prims.string Prims.list =
  fun uu____1521  -> lookup_opt "codegen-lib" (as_list as_string)
let get_debug: Prims.unit -> Prims.string Prims.list =
  fun uu____1528  -> lookup_opt "debug" (as_list as_string)
let get_debug_level: Prims.unit -> Prims.string Prims.list =
  fun uu____1535  -> lookup_opt "debug_level" (as_list as_string)
let get_dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1542  -> lookup_opt "dep" (as_option as_string)
let get_detail_errors: Prims.unit -> Prims.bool =
  fun uu____1547  -> lookup_opt "detail_errors" as_bool
let get_detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____1550  -> lookup_opt "detail_hint_replay" as_bool
let get_doc: Prims.unit -> Prims.bool =
  fun uu____1553  -> lookup_opt "doc" as_bool
let get_dump_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1558  -> lookup_opt "dump_module" (as_list as_string)
let get_eager_inference: Prims.unit -> Prims.bool =
  fun uu____1563  -> lookup_opt "eager_inference" as_bool
let get_expose_interfaces: Prims.unit -> Prims.bool =
  fun uu____1566  -> lookup_opt "expose_interfaces" as_bool
let get_extract_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1571  -> lookup_opt "extract_module" (as_list as_string)
let get_extract_namespace: Prims.unit -> Prims.string Prims.list =
  fun uu____1578  -> lookup_opt "extract_namespace" (as_list as_string)
let get_fs_typ_app: Prims.unit -> Prims.bool =
  fun uu____1583  -> lookup_opt "fs_typ_app" as_bool
let get_fstar_home: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1588  -> lookup_opt "fstar_home" (as_option as_string)
let get_gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1595  -> lookup_opt "gen_native_tactics" (as_option as_string)
let get_hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____1600  -> lookup_opt "hide_uvar_nums" as_bool
let get_hint_info: Prims.unit -> Prims.bool =
  fun uu____1603  -> lookup_opt "hint_info" as_bool
let get_hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1608  -> lookup_opt "hint_file" (as_option as_string)
let get_in: Prims.unit -> Prims.bool =
  fun uu____1613  -> lookup_opt "in" as_bool
let get_ide: Prims.unit -> Prims.bool =
  fun uu____1616  -> lookup_opt "ide" as_bool
let get_include: Prims.unit -> Prims.string Prims.list =
  fun uu____1621  -> lookup_opt "include" (as_list as_string)
let get_indent: Prims.unit -> Prims.bool =
  fun uu____1626  -> lookup_opt "indent" as_bool
let get_initial_fuel: Prims.unit -> Prims.int =
  fun uu____1629  -> lookup_opt "initial_fuel" as_int
let get_initial_ifuel: Prims.unit -> Prims.int =
  fun uu____1632  -> lookup_opt "initial_ifuel" as_int
let get_lax: Prims.unit -> Prims.bool =
  fun uu____1635  -> lookup_opt "lax" as_bool
let get_load: Prims.unit -> Prims.string Prims.list =
  fun uu____1640  -> lookup_opt "load" (as_list as_string)
let get_log_queries: Prims.unit -> Prims.bool =
  fun uu____1645  -> lookup_opt "log_queries" as_bool
let get_log_types: Prims.unit -> Prims.bool =
  fun uu____1648  -> lookup_opt "log_types" as_bool
let get_max_fuel: Prims.unit -> Prims.int =
  fun uu____1651  -> lookup_opt "max_fuel" as_int
let get_max_ifuel: Prims.unit -> Prims.int =
  fun uu____1654  -> lookup_opt "max_ifuel" as_int
let get_min_fuel: Prims.unit -> Prims.int =
  fun uu____1657  -> lookup_opt "min_fuel" as_int
let get_MLish: Prims.unit -> Prims.bool =
  fun uu____1660  -> lookup_opt "MLish" as_bool
let get_n_cores: Prims.unit -> Prims.int =
  fun uu____1663  -> lookup_opt "n_cores" as_int
let get_no_default_includes: Prims.unit -> Prims.bool =
  fun uu____1666  -> lookup_opt "no_default_includes" as_bool
let get_no_extract: Prims.unit -> Prims.string Prims.list =
  fun uu____1671  -> lookup_opt "no_extract" (as_list as_string)
let get_no_location_info: Prims.unit -> Prims.bool =
  fun uu____1676  -> lookup_opt "no_location_info" as_bool
let get_odir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1681  -> lookup_opt "odir" (as_option as_string)
let get_ugly: Prims.unit -> Prims.bool =
  fun uu____1686  -> lookup_opt "ugly" as_bool
let get_prims: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1691  -> lookup_opt "prims" (as_option as_string)
let get_print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____1696  -> lookup_opt "print_bound_var_types" as_bool
let get_print_effect_args: Prims.unit -> Prims.bool =
  fun uu____1699  -> lookup_opt "print_effect_args" as_bool
let get_print_full_names: Prims.unit -> Prims.bool =
  fun uu____1702  -> lookup_opt "print_full_names" as_bool
let get_print_implicits: Prims.unit -> Prims.bool =
  fun uu____1705  -> lookup_opt "print_implicits" as_bool
let get_print_universes: Prims.unit -> Prims.bool =
  fun uu____1708  -> lookup_opt "print_universes" as_bool
let get_print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____1711  -> lookup_opt "print_z3_statistics" as_bool
let get_prn: Prims.unit -> Prims.bool =
  fun uu____1714  -> lookup_opt "prn" as_bool
let get_query_stats: Prims.unit -> Prims.bool =
  fun uu____1717  -> lookup_opt "query_stats" as_bool
let get_record_hints: Prims.unit -> Prims.bool =
  fun uu____1720  -> lookup_opt "record_hints" as_bool
let get_reuse_hint_for:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1725  -> lookup_opt "reuse_hint_for" (as_option as_string)
let get_silent: Prims.unit -> Prims.bool =
  fun uu____1730  -> lookup_opt "silent" as_bool
let get_smt: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1735  -> lookup_opt "smt" (as_option as_string)
let get_smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____1740  -> lookup_opt "smtencoding.elim_box" as_bool
let get_smtencoding_nl_arith_repr: Prims.unit -> Prims.string =
  fun uu____1743  -> lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr: Prims.unit -> Prims.string =
  fun uu____1746  -> lookup_opt "smtencoding.l_arith_repr" as_string
let get_split_cases: Prims.unit -> Prims.int =
  fun uu____1749  -> lookup_opt "split_cases" as_int
let get_tactic_raw_binders: Prims.unit -> Prims.bool =
  fun uu____1752  -> lookup_opt "tactic_raw_binders" as_bool
let get_tactic_trace: Prims.unit -> Prims.bool =
  fun uu____1755  -> lookup_opt "tactic_trace" as_bool
let get_tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____1758  -> lookup_opt "tactic_trace_d" as_int
let get_timing: Prims.unit -> Prims.bool =
  fun uu____1761  -> lookup_opt "timing" as_bool
let get_trace_error: Prims.unit -> Prims.bool =
  fun uu____1764  -> lookup_opt "trace_error" as_bool
let get_unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____1767  -> lookup_opt "unthrottle_inductives" as_bool
let get_unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____1770  -> lookup_opt "unsafe_tactic_exec" as_bool
let get_use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____1773  -> lookup_opt "use_eq_at_higher_order" as_bool
let get_use_hints: Prims.unit -> Prims.bool =
  fun uu____1776  -> lookup_opt "use_hints" as_bool
let get_use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____1779  -> lookup_opt "use_hint_hashes" as_bool
let get_use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1784  -> lookup_opt "use_native_tactics" (as_option as_string)
let get_use_tactics: Prims.unit -> Prims.bool =
  fun uu____1789  ->
    let uu____1790 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____1790
let get_using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1797  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let get_verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1808  -> lookup_opt "verify_module" (as_list as_string)
let get___temp_no_proj: Prims.unit -> Prims.string Prims.list =
  fun uu____1815  -> lookup_opt "__temp_no_proj" (as_list as_string)
let get_version: Prims.unit -> Prims.bool =
  fun uu____1820  -> lookup_opt "version" as_bool
let get_warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____1823  -> lookup_opt "warn_default_effects" as_bool
let get_z3cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____1828  -> lookup_opt "z3cliopt" (as_list as_string)
let get_z3refresh: Prims.unit -> Prims.bool =
  fun uu____1833  -> lookup_opt "z3refresh" as_bool
let get_z3rlimit: Prims.unit -> Prims.int =
  fun uu____1836  -> lookup_opt "z3rlimit" as_int
let get_z3rlimit_factor: Prims.unit -> Prims.int =
  fun uu____1839  -> lookup_opt "z3rlimit_factor" as_int
let get_z3seed: Prims.unit -> Prims.int =
  fun uu____1842  -> lookup_opt "z3seed" as_int
let get_use_two_phase_tc: Prims.unit -> Prims.bool =
  fun uu____1845  -> lookup_opt "use_two_phase_tc" as_bool
let get_no_positivity: Prims.unit -> Prims.bool =
  fun uu____1848  -> lookup_opt "__no_positivity" as_bool
let get_ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____1851  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool
let get_warn_error: Prims.unit -> Prims.string =
  fun uu____1854  -> lookup_opt "warn_error" as_string
let dlevel: Prims.string -> debug_level_t =
  fun uu___40_1857  ->
    match uu___40_1857 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let one_debug_level_geq: debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1865 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let debug_level_geq: debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____1869 = get_debug_level () in
    FStar_All.pipe_right uu____1869
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
let universe_include_path_base_dirs: Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"]
let _version: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _platform: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _compiler: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _date: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _commit: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let display_version: Prims.unit -> Prims.unit =
  fun uu____1960  ->
    let uu____1961 =
      let uu____1962 = FStar_ST.op_Bang _version in
      let uu____2011 = FStar_ST.op_Bang _platform in
      let uu____2060 = FStar_ST.op_Bang _compiler in
      let uu____2109 = FStar_ST.op_Bang _date in
      let uu____2158 = FStar_ST.op_Bang _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1962
        uu____2011 uu____2060 uu____2109 uu____2158 in
    FStar_Util.print_string uu____1961
let display_usage_aux:
  'Auu____2210 'Auu____2211 .
    ('Auu____2211,Prims.string,'Auu____2210 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2258  ->
         match uu____2258 with
         | (uu____2269,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2280 =
                      let uu____2281 = FStar_Util.colorize_bold flag in
                      FStar_Util.format1 "  --%s\n" uu____2281 in
                    FStar_Util.print_string uu____2280
                  else
                    (let uu____2283 =
                       let uu____2284 = FStar_Util.colorize_bold flag in
                       FStar_Util.format2 "  --%s  %s\n" uu____2284 doc in
                     FStar_Util.print_string uu____2283)
              | FStar_Getopt.OneArg (uu____2285,argname) ->
                  if doc = ""
                  then
                    let uu____2291 =
                      let uu____2292 = FStar_Util.colorize_bold flag in
                      let uu____2293 = FStar_Util.colorize_bold argname in
                      FStar_Util.format2 "  --%s %s\n" uu____2292 uu____2293 in
                    FStar_Util.print_string uu____2291
                  else
                    (let uu____2295 =
                       let uu____2296 = FStar_Util.colorize_bold flag in
                       let uu____2297 = FStar_Util.colorize_bold argname in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2296
                         uu____2297 doc in
                     FStar_Util.print_string uu____2295))) specs
let mk_spec:
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____2321 = o in
    match uu____2321 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2351 =
                let uu____2352 = f () in set_option name uu____2352 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2363 = f x in set_option name uu____2363 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2377 = lookup_opt name (as_option as_list') in
        FStar_Util.dflt [] uu____2377 in
      mk_list (value :: prev_values)
let reverse_accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let uu____2396 =
        let uu____2399 = lookup_opt name as_list' in
        FStar_List.append uu____2399 [value] in
      mk_list uu____2396
let accumulate_string:
  'Auu____2408 .
    Prims.string ->
      ('Auu____2408 -> Prims.string) -> 'Auu____2408 -> Prims.unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2426 =
          let uu____2427 =
            let uu____2428 = post_processor value in mk_string uu____2428 in
          accumulated_option name uu____2427 in
        set_option name uu____2426
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
    match projectee with | Const _0 -> true | uu____2506 -> false
let __proj__Const__item___0: opt_type -> option_val =
  fun projectee  -> match projectee with | Const _0 -> _0
let uu___is_IntStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2518 -> false
let __proj__IntStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | IntStr _0 -> _0
let uu___is_BoolStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2529 -> false
let uu___is_PathStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2534 -> false
let __proj__PathStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | PathStr _0 -> _0
let uu___is_SimpleStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2546 -> false
let __proj__SimpleStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0
let uu___is_EnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2560 -> false
let __proj__EnumStr__item___0: opt_type -> Prims.string Prims.list =
  fun projectee  -> match projectee with | EnumStr _0 -> _0
let uu___is_OpenEnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2584 -> false
let __proj__OpenEnumStr__item___0:
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0
let uu___is_PostProcessed: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2620 -> false
let __proj__PostProcessed__item___0:
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0
let uu___is_Accumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2650 -> false
let __proj__Accumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | Accumulated _0 -> _0
let uu___is_ReverseAccumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2662 -> false
let __proj__ReverseAccumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0
let uu___is_WithSideEffect: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2680 -> false
let __proj__WithSideEffect__item___0:
  opt_type ->
    (Prims.unit -> Prims.unit,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | WithSideEffect _0 -> _0
exception InvalidArgument of Prims.string
let uu___is_InvalidArgument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2712 -> true
    | uu____2713 -> false
let __proj__InvalidArgument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2720 -> uu____2720
let rec parse_opt_val: Prims.string -> opt_type -> Prims.string -> option_val
  =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2734 ->
              let uu____2735 = FStar_Util.safe_int_of_string str_val in
              (match uu____2735 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2739 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name) in
              mk_bool uu____2739
          | PathStr uu____2742 -> mk_path str_val
          | SimpleStr uu____2743 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2748 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2761 = parse_opt_val opt_name elem_spec str_val in
              pp uu____2761
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
            let uu____2778 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1 in
            failwith uu____2778
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
    | PostProcessed (uu____2811,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2819,elem_spec) -> desc_of_opt_type elem_spec
let rec arg_spec_of_opt_type:
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ in
      let uu____2838 = desc_of_opt_type typ in
      match uu____2838 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2844  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
let pp_validate_dir: option_val -> option_val =
  fun p  -> let pp = as_string p in FStar_Util.mkdir false pp; p
let pp_lowercase: option_val -> option_val =
  fun s  ->
    let uu____2856 =
      let uu____2857 = as_string s in FStar_String.lowercase uu____2857 in
    mk_string uu____2856
let rec specs_with_types:
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun uu____2874  ->
    let uu____2885 =
      let uu____2896 =
        let uu____2907 =
          let uu____2916 = let uu____2917 = mk_bool true in Const uu____2917 in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2916,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying") in
        let uu____2918 =
          let uu____2929 =
            let uu____2940 =
              let uu____2951 =
                let uu____2962 =
                  let uu____2973 =
                    let uu____2984 =
                      let uu____2993 =
                        let uu____2994 = mk_bool true in Const uu____2994 in
                      (FStar_Getopt.noshort, "detail_errors", uu____2993,
                        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1") in
                    let uu____2995 =
                      let uu____3006 =
                        let uu____3015 =
                          let uu____3016 = mk_bool true in Const uu____3016 in
                        (FStar_Getopt.noshort, "detail_hint_replay",
                          uu____3015,
                          "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1") in
                      let uu____3017 =
                        let uu____3028 =
                          let uu____3037 =
                            let uu____3038 = mk_bool true in Const uu____3038 in
                          (FStar_Getopt.noshort, "doc", uu____3037,
                            "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.") in
                        let uu____3039 =
                          let uu____3050 =
                            let uu____3061 =
                              let uu____3070 =
                                let uu____3071 = mk_bool true in
                                Const uu____3071 in
                              (FStar_Getopt.noshort, "eager_inference",
                                uu____3070,
                                "Solve all type-inference constraints eagerly; more efficient but at the cost of generality") in
                            let uu____3072 =
                              let uu____3083 =
                                let uu____3094 =
                                  let uu____3105 =
                                    let uu____3114 =
                                      let uu____3115 = mk_bool true in
                                      Const uu____3115 in
                                    (FStar_Getopt.noshort,
                                      "expose_interfaces", uu____3114,
                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)") in
                                  let uu____3116 =
                                    let uu____3127 =
                                      let uu____3138 =
                                        let uu____3149 =
                                          let uu____3158 =
                                            let uu____3159 = mk_bool true in
                                            Const uu____3159 in
                                          (FStar_Getopt.noshort,
                                            "hide_uvar_nums", uu____3158,
                                            "Don't print unification variable numbers") in
                                        let uu____3160 =
                                          let uu____3171 =
                                            let uu____3182 =
                                              let uu____3191 =
                                                let uu____3192 = mk_bool true in
                                                Const uu____3192 in
                                              (FStar_Getopt.noshort,
                                                "hint_info", uu____3191,
                                                "Print information regarding hints (deprecated; use --query_stats instead)") in
                                            let uu____3193 =
                                              let uu____3204 =
                                                let uu____3213 =
                                                  let uu____3214 =
                                                    mk_bool true in
                                                  Const uu____3214 in
                                                (FStar_Getopt.noshort, "in",
                                                  uu____3213,
                                                  "Legacy interactive mode; reads input from stdin") in
                                              let uu____3215 =
                                                let uu____3226 =
                                                  let uu____3235 =
                                                    let uu____3236 =
                                                      mk_bool true in
                                                    Const uu____3236 in
                                                  (FStar_Getopt.noshort,
                                                    "ide", uu____3235,
                                                    "JSON-based interactive mode for IDEs") in
                                                let uu____3237 =
                                                  let uu____3248 =
                                                    let uu____3259 =
                                                      let uu____3268 =
                                                        let uu____3269 =
                                                          mk_bool true in
                                                        Const uu____3269 in
                                                      (FStar_Getopt.noshort,
                                                        "indent", uu____3268,
                                                        "Parses and outputs the files on the command line") in
                                                    let uu____3270 =
                                                      let uu____3281 =
                                                        let uu____3292 =
                                                          let uu____3303 =
                                                            let uu____3312 =
                                                              let uu____3313
                                                                =
                                                                mk_bool true in
                                                              Const
                                                                uu____3313 in
                                                            (FStar_Getopt.noshort,
                                                              "lax",
                                                              uu____3312,
                                                              "Run the lax-type checker only (admit all verification conditions)") in
                                                          let uu____3314 =
                                                            let uu____3325 =
                                                              let uu____3336
                                                                =
                                                                let uu____3345
                                                                  =
                                                                  let uu____3346
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                  Const
                                                                    uu____3346 in
                                                                (FStar_Getopt.noshort,
                                                                  "log_types",
                                                                  uu____3345,
                                                                  "Print types computed for data/val/let-bindings") in
                                                              let uu____3347
                                                                =
                                                                let uu____3358
                                                                  =
                                                                  let uu____3367
                                                                    =
                                                                    let uu____3368
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3368 in
                                                                  (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3367,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go") in
                                                                let uu____3369
                                                                  =
                                                                  let uu____3380
                                                                    =
                                                                    let uu____3391
                                                                    =
                                                                    let uu____3402
                                                                    =
                                                                    let uu____3413
                                                                    =
                                                                    let uu____3422
                                                                    =
                                                                    let uu____3423
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3423 in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3422,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)") in
                                                                    let uu____3424
                                                                    =
                                                                    let uu____3435
                                                                    =
                                                                    let uu____3446
                                                                    =
                                                                    let uu____3455
                                                                    =
                                                                    let uu____3456
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3456 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3455,
                                                                    "Ignore the default module search paths") in
                                                                    let uu____3457
                                                                    =
                                                                    let uu____3468
                                                                    =
                                                                    let uu____3479
                                                                    =
                                                                    let uu____3488
                                                                    =
                                                                    let uu____3489
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3489 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3488,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)") in
                                                                    let uu____3490
                                                                    =
                                                                    let uu____3501
                                                                    =
                                                                    let uu____3512
                                                                    =
                                                                    let uu____3523
                                                                    =
                                                                    let uu____3532
                                                                    =
                                                                    let uu____3533
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3533 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3532,
                                                                    "Print the types of bound variables") in
                                                                    let uu____3534
                                                                    =
                                                                    let uu____3545
                                                                    =
                                                                    let uu____3554
                                                                    =
                                                                    let uu____3555
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3555 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3554,
                                                                    "Print inferred predicate transformers for all computation types") in
                                                                    let uu____3556
                                                                    =
                                                                    let uu____3567
                                                                    =
                                                                    let uu____3576
                                                                    =
                                                                    let uu____3577
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3577 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3576,
                                                                    "Print full names of variables") in
                                                                    let uu____3578
                                                                    =
                                                                    let uu____3589
                                                                    =
                                                                    let uu____3598
                                                                    =
                                                                    let uu____3599
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3599 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3598,
                                                                    "Print implicit arguments") in
                                                                    let uu____3600
                                                                    =
                                                                    let uu____3611
                                                                    =
                                                                    let uu____3620
                                                                    =
                                                                    let uu____3621
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3621 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3620,
                                                                    "Print universes") in
                                                                    let uu____3622
                                                                    =
                                                                    let uu____3633
                                                                    =
                                                                    let uu____3642
                                                                    =
                                                                    let uu____3643
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3643 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3642,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)") in
                                                                    let uu____3644
                                                                    =
                                                                    let uu____3655
                                                                    =
                                                                    let uu____3664
                                                                    =
                                                                    let uu____3665
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3665 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3664,
                                                                    "Print full names (deprecated; use --print_full_names instead)") in
                                                                    let uu____3666
                                                                    =
                                                                    let uu____3677
                                                                    =
                                                                    let uu____3686
                                                                    =
                                                                    let uu____3687
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3687 in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3686,
                                                                    "Print SMT query statistics") in
                                                                    let uu____3688
                                                                    =
                                                                    let uu____3699
                                                                    =
                                                                    let uu____3708
                                                                    =
                                                                    let uu____3709
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3709 in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3708,
                                                                    "Record a database of hints for efficient proof replay") in
                                                                    let uu____3710
                                                                    =
                                                                    let uu____3721
                                                                    =
                                                                    let uu____3732
                                                                    =
                                                                    let uu____3741
                                                                    =
                                                                    let uu____3742
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3742 in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3741,
                                                                    " ") in
                                                                    let uu____3743
                                                                    =
                                                                    let uu____3754
                                                                    =
                                                                    let uu____3765
                                                                    =
                                                                    let uu____3776
                                                                    =
                                                                    let uu____3787
                                                                    =
                                                                    let uu____3798
                                                                    =
                                                                    let uu____3809
                                                                    =
                                                                    let uu____3818
                                                                    =
                                                                    let uu____3819
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3819 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____3818,
                                                                    "Do not use the lexical scope of tactics to improve binder names") in
                                                                    let uu____3820
                                                                    =
                                                                    let uu____3831
                                                                    =
                                                                    let uu____3840
                                                                    =
                                                                    let uu____3841
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3841 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3840,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)") in
                                                                    let uu____3842
                                                                    =
                                                                    let uu____3853
                                                                    =
                                                                    let uu____3864
                                                                    =
                                                                    let uu____3873
                                                                    =
                                                                    let uu____3874
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3874 in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3873,
                                                                    "Print the time it takes to verify each top-level definition") in
                                                                    let uu____3875
                                                                    =
                                                                    let uu____3886
                                                                    =
                                                                    let uu____3895
                                                                    =
                                                                    let uu____3896
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3896 in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3895,
                                                                    "Don't print an error message; show an exception trace instead") in
                                                                    let uu____3897
                                                                    =
                                                                    let uu____3908
                                                                    =
                                                                    let uu____3917
                                                                    =
                                                                    let uu____3918
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3918 in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3917,
                                                                    "Emit output formatted for debugging") in
                                                                    let uu____3919
                                                                    =
                                                                    let uu____3930
                                                                    =
                                                                    let uu____3939
                                                                    =
                                                                    let uu____3940
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3940 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____3939,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)") in
                                                                    let uu____3941
                                                                    =
                                                                    let uu____3952
                                                                    =
                                                                    let uu____3961
                                                                    =
                                                                    let uu____3962
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3962 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____3961,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.") in
                                                                    let uu____3963
                                                                    =
                                                                    let uu____3974
                                                                    =
                                                                    let uu____3983
                                                                    =
                                                                    let uu____3984
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3984 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____3983,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)") in
                                                                    let uu____3985
                                                                    =
                                                                    let uu____3996
                                                                    =
                                                                    let uu____4005
                                                                    =
                                                                    let uu____4006
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4006 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4005,
                                                                    "Use a previously recorded hints database for proof replay") in
                                                                    let uu____4007
                                                                    =
                                                                    let uu____4018
                                                                    =
                                                                    let uu____4027
                                                                    =
                                                                    let uu____4028
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4028 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4027,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database") in
                                                                    let uu____4029
                                                                    =
                                                                    let uu____4040
                                                                    =
                                                                    let uu____4051
                                                                    =
                                                                    let uu____4060
                                                                    =
                                                                    let uu____4061
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4061 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4060,
                                                                    "Do not run the tactic engine before discharging a VC") in
                                                                    let uu____4062
                                                                    =
                                                                    let uu____4073
                                                                    =
                                                                    let uu____4084
                                                                    =
                                                                    let uu____4095
                                                                    =
                                                                    let uu____4105
                                                                    =
                                                                    let uu____4106
                                                                    =
                                                                    let uu____4113
                                                                    =
                                                                    let uu____4114
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4114 in
                                                                    ((fun
                                                                    uu____4119
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____4113) in
                                                                    WithSideEffect
                                                                    uu____4106 in
                                                                    (118,
                                                                    "version",
                                                                    uu____4105,
                                                                    "Display version number") in
                                                                    let uu____4123
                                                                    =
                                                                    let uu____4135
                                                                    =
                                                                    let uu____4144
                                                                    =
                                                                    let uu____4145
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4145 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4144,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)") in
                                                                    let uu____4146
                                                                    =
                                                                    let uu____4157
                                                                    =
                                                                    let uu____4168
                                                                    =
                                                                    let uu____4177
                                                                    =
                                                                    let uu____4178
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4178 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4177,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness") in
                                                                    let uu____4179
                                                                    =
                                                                    let uu____4190
                                                                    =
                                                                    let uu____4201
                                                                    =
                                                                    let uu____4212
                                                                    =
                                                                    let uu____4223
                                                                    =
                                                                    let uu____4234
                                                                    =
                                                                    let uu____4243
                                                                    =
                                                                    let uu____4244
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4244 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4243,
                                                                    "Don't check positivity of inductive types") in
                                                                    let uu____4245
                                                                    =
                                                                    let uu____4256
                                                                    =
                                                                    let uu____4265
                                                                    =
                                                                    let uu____4266
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4266 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4265,
                                                                    "Do not eta-expand coertions in generated OCaml") in
                                                                    let uu____4267
                                                                    =
                                                                    let uu____4278
                                                                    =
                                                                    let uu____4289
                                                                    =
                                                                    let uu____4299
                                                                    =
                                                                    let uu____4300
                                                                    =
                                                                    let uu____4307
                                                                    =
                                                                    let uu____4308
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4308 in
                                                                    ((fun
                                                                    uu____4313
                                                                     ->
                                                                    (
                                                                    let uu____4315
                                                                    =
                                                                    specs () in
                                                                    display_usage_aux
                                                                    uu____4315);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____4307) in
                                                                    WithSideEffect
                                                                    uu____4300 in
                                                                    (104,
                                                                    "help",
                                                                    uu____4299,
                                                                    "Display this information") in
                                                                    [uu____4289] in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4278 in
                                                                    uu____4256
                                                                    ::
                                                                    uu____4267 in
                                                                    uu____4234
                                                                    ::
                                                                    uu____4245 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'false')")
                                                                    ::
                                                                    uu____4223 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4212 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4201 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4190 in
                                                                    uu____4168
                                                                    ::
                                                                    uu____4179 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4157 in
                                                                    uu____4135
                                                                    ::
                                                                    uu____4146 in
                                                                    uu____4095
                                                                    ::
                                                                    uu____4123 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4084 in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4073 in
                                                                    uu____4051
                                                                    ::
                                                                    uu____4062 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4040 in
                                                                    uu____4018
                                                                    ::
                                                                    uu____4029 in
                                                                    uu____3996
                                                                    ::
                                                                    uu____4007 in
                                                                    uu____3974
                                                                    ::
                                                                    uu____3985 in
                                                                    uu____3952
                                                                    ::
                                                                    uu____3963 in
                                                                    uu____3930
                                                                    ::
                                                                    uu____3941 in
                                                                    uu____3908
                                                                    ::
                                                                    uu____3919 in
                                                                    uu____3886
                                                                    ::
                                                                    uu____3897 in
                                                                    uu____3864
                                                                    ::
                                                                    uu____3875 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3853 in
                                                                    uu____3831
                                                                    ::
                                                                    uu____3842 in
                                                                    uu____3809
                                                                    ::
                                                                    uu____3820 in
                                                                    (FStar_Getopt.noshort,
                                                                    "split_cases",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Partition VC of a match into groups of <positive_integer> cases")
                                                                    ::
                                                                    uu____3798 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3787 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3776 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3765 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3754 in
                                                                    uu____3732
                                                                    ::
                                                                    uu____3743 in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3721 in
                                                                    uu____3699
                                                                    ::
                                                                    uu____3710 in
                                                                    uu____3677
                                                                    ::
                                                                    uu____3688 in
                                                                    uu____3655
                                                                    ::
                                                                    uu____3666 in
                                                                    uu____3633
                                                                    ::
                                                                    uu____3644 in
                                                                    uu____3611
                                                                    ::
                                                                    uu____3622 in
                                                                    uu____3589
                                                                    ::
                                                                    uu____3600 in
                                                                    uu____3567
                                                                    ::
                                                                    uu____3578 in
                                                                    uu____3545
                                                                    ::
                                                                    uu____3556 in
                                                                    uu____3523
                                                                    ::
                                                                    uu____3534 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3512 in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3501 in
                                                                    uu____3479
                                                                    ::
                                                                    uu____3490 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Do not extract code from this module")
                                                                    ::
                                                                    uu____3468 in
                                                                    uu____3446
                                                                    ::
                                                                    uu____3457 in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3435 in
                                                                    uu____3413
                                                                    ::
                                                                    uu____3424 in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3402 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3391 in
                                                                  (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (
                                                                    IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3380 in
                                                                uu____3358 ::
                                                                  uu____3369 in
                                                              uu____3336 ::
                                                                uu____3347 in
                                                            (FStar_Getopt.noshort,
                                                              "load",
                                                              (ReverseAccumulated
                                                                 (PathStr
                                                                    "module")),
                                                              "Load compiled module")
                                                              :: uu____3325 in
                                                          uu____3303 ::
                                                            uu____3314 in
                                                        (FStar_Getopt.noshort,
                                                          "initial_ifuel",
                                                          (IntStr
                                                             "non-negative integer"),
                                                          "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                          :: uu____3292 in
                                                      (FStar_Getopt.noshort,
                                                        "initial_fuel",
                                                        (IntStr
                                                           "non-negative integer"),
                                                        "Number of unrolling of recursive functions to try initially (default 2)")
                                                        :: uu____3281 in
                                                    uu____3259 :: uu____3270 in
                                                  (FStar_Getopt.noshort,
                                                    "include",
                                                    (ReverseAccumulated
                                                       (PathStr "path")),
                                                    "A directory in which to search for files included on the command line")
                                                    :: uu____3248 in
                                                uu____3226 :: uu____3237 in
                                              uu____3204 :: uu____3215 in
                                            uu____3182 :: uu____3193 in
                                          (FStar_Getopt.noshort, "hint_file",
                                            (PathStr "path"),
                                            "Read/write hints to <path> (instead of module-specific hints files)")
                                            :: uu____3171 in
                                        uu____3149 :: uu____3160 in
                                      (FStar_Getopt.noshort,
                                        "gen_native_tactics",
                                        (PathStr "[path]"),
                                        "Compile all user tactics used in the module in <path>")
                                        :: uu____3138 in
                                    (FStar_Getopt.noshort, "fstar_home",
                                      (PathStr "dir"),
                                      "Set the FSTAR_HOME variable to <dir>")
                                      :: uu____3127 in
                                  uu____3105 :: uu____3116 in
                                (FStar_Getopt.noshort, "extract_namespace",
                                  (Accumulated
                                     (PostProcessed
                                        (pp_lowercase,
                                          (SimpleStr "namespace name")))),
                                  "Only extract modules in the specified namespace")
                                  :: uu____3094 in
                              (FStar_Getopt.noshort, "extract_module",
                                (Accumulated
                                   (PostProcessed
                                      (pp_lowercase,
                                        (SimpleStr "module_name")))),
                                "Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                :: uu____3083 in
                            uu____3061 :: uu____3072 in
                          (FStar_Getopt.noshort, "dump_module",
                            (Accumulated (SimpleStr "module_name")), "") ::
                            uu____3050 in
                        uu____3028 :: uu____3039 in
                      uu____3006 :: uu____3017 in
                    uu____2984 :: uu____2995 in
                  (FStar_Getopt.noshort, "dep",
                    (EnumStr ["make"; "graph"; "full"]),
                    "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                    :: uu____2973 in
                (FStar_Getopt.noshort, "debug_level",
                  (Accumulated
                     (OpenEnumStr
                        (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                  "Control the verbosity of debugging info") :: uu____2962 in
              (FStar_Getopt.noshort, "debug",
                (Accumulated (SimpleStr "module_name")),
                "Print lots of debugging information while checking module")
                :: uu____2951 in
            (FStar_Getopt.noshort, "codegen-lib",
              (Accumulated (SimpleStr "namespace")),
              "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
              :: uu____2940 in
          (FStar_Getopt.noshort, "codegen",
            (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "tactics"]),
            "Generate code for execution") :: uu____2929 in
        uu____2907 :: uu____2918 in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2896 in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2885
and specs: Prims.unit -> FStar_Getopt.opt Prims.list =
  fun uu____5021  ->
    let uu____5024 = specs_with_types () in
    FStar_List.map
      (fun uu____5049  ->
         match uu____5049 with
         | (short,long,typ,doc) ->
             let uu____5062 =
               let uu____5073 = arg_spec_of_opt_type long typ in
               (short, long, uu____5073, doc) in
             mk_spec uu____5062) uu____5024
let settable: Prims.string -> Prims.bool =
  fun uu___41_5080  ->
    match uu___41_5080 with
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
    | uu____5081 -> false
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
       (fun uu____5138  ->
          match uu____5138 with
          | (uu____5149,x,uu____5151,uu____5152) -> settable x))
let resettable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5198  ->
          match uu____5198 with
          | (uu____5209,x,uu____5211,uu____5212) -> resettable x))
let display_usage: Prims.unit -> Prims.unit =
  fun uu____5219  ->
    let uu____5220 = specs () in display_usage_aux uu____5220
let fstar_home: Prims.unit -> Prims.string =
  fun uu____5235  ->
    let uu____5236 = get_fstar_home () in
    match uu____5236 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        ((let uu____5242 =
            let uu____5247 = mk_string x1 in ("fstar_home", uu____5247) in
          set_option' uu____5242);
         x1)
    | FStar_Pervasives_Native.Some x -> x
exception File_argument of Prims.string
let uu___is_File_argument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____5255 -> true
    | uu____5256 -> false
let __proj__File_argument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____5263 -> uu____5263
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
          let uu____5307 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____5307
let file_list_: Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let parse_cmd_line:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____5329  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5334 =
             let uu____5337 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____5337 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____5334) in
    let uu____5444 =
      let uu____5447 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5447 in
    (res, uu____5444)
let file_list: Prims.unit -> Prims.string Prims.list =
  fun uu____5508  -> FStar_ST.op_Bang file_list_
let restore_cmd_line_options: Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____5570 = specs () in
       FStar_Getopt.parse_cmdline uu____5570 (fun x  -> ()) in
     (let uu____5576 =
        let uu____5581 =
          let uu____5582 = FStar_List.map mk_string old_verify_module in
          List uu____5582 in
        ("verify_module", uu____5581) in
      set_option' uu____5576);
     r)
let module_name_of_file_name: Prims.string -> Prims.string =
  fun f  ->
    let f1 = FStar_Util.basename f in
    let f2 =
      let uu____5590 =
        let uu____5591 =
          let uu____5592 =
            let uu____5593 = FStar_Util.get_file_extension f1 in
            FStar_String.length uu____5593 in
          (FStar_String.length f1) - uu____5592 in
        uu____5591 - (Prims.parse_int "1") in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5590 in
    FStar_String.lowercase f2
let should_verify: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5597 = get_lax () in
    if uu____5597
    then false
    else
      (let l = get_verify_module () in
       FStar_List.contains (FStar_String.lowercase m) l)
let should_verify_file: Prims.string -> Prims.bool =
  fun fn  ->
    let uu____5605 = module_name_of_file_name fn in should_verify uu____5605
let dont_gen_projectors: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5609 = get___temp_no_proj () in
    FStar_List.contains m uu____5609
let should_print_message: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5615 = should_verify m in
    if uu____5615 then m <> "Prims" else false
let include_path: Prims.unit -> Prims.string Prims.list =
  fun uu____5621  ->
    let uu____5622 = get_no_default_includes () in
    if uu____5622
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____5630 =
         let uu____5633 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____5633
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____5646 =
         let uu____5649 = get_include () in
         FStar_List.append uu____5649 ["."] in
       FStar_List.append uu____5630 uu____5646)
let find_file: Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____5657 = FStar_Util.is_path_absolute filename in
    if uu____5657
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5664 =
         let uu____5667 = include_path () in FStar_List.rev uu____5667 in
       FStar_Util.find_map uu____5664
         (fun p  ->
            let path = FStar_Util.join_paths p filename in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
let prims: Prims.unit -> Prims.string =
  fun uu____5679  ->
    let uu____5680 = get_prims () in
    match uu____5680 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst" in
        let uu____5684 = find_file filename in
        (match uu____5684 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5688 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename in
             failwith uu____5688)
    | FStar_Pervasives_Native.Some x -> x
let prims_basename: Prims.unit -> Prims.string =
  fun uu____5692  ->
    let uu____5693 = prims () in FStar_Util.basename uu____5693
let pervasives: Prims.unit -> Prims.string =
  fun uu____5696  ->
    let filename = "FStar.Pervasives.fst" in
    let uu____5698 = find_file filename in
    match uu____5698 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5702 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5702
let pervasives_basename: Prims.unit -> Prims.string =
  fun uu____5705  ->
    let uu____5706 = pervasives () in FStar_Util.basename uu____5706
let pervasives_native_basename: Prims.unit -> Prims.string =
  fun uu____5709  ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____5711 = find_file filename in
    match uu____5711 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5715 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5715
let prepend_output_dir: Prims.string -> Prims.string =
  fun fname  ->
    let uu____5719 = get_odir () in
    match uu____5719 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
let __temp_no_proj: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5726 = get___temp_no_proj () in
    FStar_All.pipe_right uu____5726 (FStar_List.contains s)
let admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____5733  -> get_admit_smt_queries ()
let admit_except: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5738  -> get_admit_except ()
let cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____5741  -> get_cache_checked_modules ()
let codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5746  -> get_codegen ()
let codegen_libs: Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____5753  ->
    let uu____5754 = get_codegen_lib () in
    FStar_All.pipe_right uu____5754
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
let debug_any: Prims.unit -> Prims.bool =
  fun uu____5769  -> let uu____5770 = get_debug () in uu____5770 <> []
let debug_at_level: Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      (let uu____5783 = get_debug () in
       FStar_All.pipe_right uu____5783 (FStar_List.contains modul)) &&
        (debug_level_geq level)
let dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5792  -> get_dep ()
let detail_errors: Prims.unit -> Prims.bool =
  fun uu____5795  -> get_detail_errors ()
let detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____5798  -> get_detail_hint_replay ()
let doc: Prims.unit -> Prims.bool = fun uu____5801  -> get_doc ()
let dump_module: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5805 = get_dump_module () in
    FStar_All.pipe_right uu____5805 (FStar_List.contains s)
let eager_inference: Prims.unit -> Prims.bool =
  fun uu____5812  -> get_eager_inference ()
let expose_interfaces: Prims.unit -> Prims.bool =
  fun uu____5815  -> get_expose_interfaces ()
let fs_typ_app: Prims.string -> Prims.bool =
  fun filename  ->
    let uu____5819 = FStar_ST.op_Bang light_off_files in
    FStar_List.contains filename uu____5819
let gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5878  -> get_gen_native_tactics ()
let full_context_dependency: Prims.unit -> Prims.bool =
  fun uu____5881  -> true
let hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____5884  -> get_hide_uvar_nums ()
let hint_info: Prims.unit -> Prims.bool =
  fun uu____5887  -> (get_hint_info ()) || (get_query_stats ())
let hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5892  -> get_hint_file ()
let ide: Prims.unit -> Prims.bool = fun uu____5895  -> get_ide ()
let indent: Prims.unit -> Prims.bool = fun uu____5898  -> get_indent ()
let initial_fuel: Prims.unit -> Prims.int =
  fun uu____5901  ->
    let uu____5902 = get_initial_fuel () in
    let uu____5903 = get_max_fuel () in Prims.min uu____5902 uu____5903
let initial_ifuel: Prims.unit -> Prims.int =
  fun uu____5906  ->
    let uu____5907 = get_initial_ifuel () in
    let uu____5908 = get_max_ifuel () in Prims.min uu____5907 uu____5908
let interactive: Prims.unit -> Prims.bool =
  fun uu____5911  -> (get_in ()) || (get_ide ())
let lax: Prims.unit -> Prims.bool = fun uu____5914  -> get_lax ()
let load: Prims.unit -> Prims.string Prims.list =
  fun uu____5919  -> get_load ()
let legacy_interactive: Prims.unit -> Prims.bool =
  fun uu____5922  -> get_in ()
let log_queries: Prims.unit -> Prims.bool =
  fun uu____5925  -> get_log_queries ()
let log_types: Prims.unit -> Prims.bool = fun uu____5928  -> get_log_types ()
let max_fuel: Prims.unit -> Prims.int = fun uu____5931  -> get_max_fuel ()
let max_ifuel: Prims.unit -> Prims.int = fun uu____5934  -> get_max_ifuel ()
let min_fuel: Prims.unit -> Prims.int = fun uu____5937  -> get_min_fuel ()
let ml_ish: Prims.unit -> Prims.bool = fun uu____5940  -> get_MLish ()
let set_ml_ish: Prims.unit -> Prims.unit =
  fun uu____5943  -> set_option "MLish" (Bool true)
let n_cores: Prims.unit -> Prims.int = fun uu____5946  -> get_n_cores ()
let no_default_includes: Prims.unit -> Prims.bool =
  fun uu____5949  -> get_no_default_includes ()
let no_extract: Prims.string -> Prims.bool =
  fun s  ->
    let s1 = FStar_String.lowercase s in
    let uu____5954 = get_no_extract () in
    FStar_All.pipe_right uu____5954
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
let no_location_info: Prims.unit -> Prims.bool =
  fun uu____5963  -> get_no_location_info ()
let output_dir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5968  -> get_odir ()
let ugly: Prims.unit -> Prims.bool = fun uu____5971  -> get_ugly ()
let print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____5974  -> get_print_bound_var_types ()
let print_effect_args: Prims.unit -> Prims.bool =
  fun uu____5977  -> get_print_effect_args ()
let print_implicits: Prims.unit -> Prims.bool =
  fun uu____5980  -> get_print_implicits ()
let print_real_names: Prims.unit -> Prims.bool =
  fun uu____5983  -> (get_prn ()) || (get_print_full_names ())
let print_universes: Prims.unit -> Prims.bool =
  fun uu____5986  -> get_print_universes ()
let print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____5989  -> (get_print_z3_statistics ()) || (get_query_stats ())
let query_stats: Prims.unit -> Prims.bool =
  fun uu____5992  -> get_query_stats ()
let record_hints: Prims.unit -> Prims.bool =
  fun uu____5995  -> get_record_hints ()
let reuse_hint_for: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____6000  -> get_reuse_hint_for ()
let silent: Prims.unit -> Prims.bool = fun uu____6003  -> get_silent ()
let smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____6006  -> get_smtencoding_elim_box ()
let smtencoding_nl_arith_native: Prims.unit -> Prims.bool =
  fun uu____6009  ->
    let uu____6010 = get_smtencoding_nl_arith_repr () in
    uu____6010 = "native"
let smtencoding_nl_arith_wrapped: Prims.unit -> Prims.bool =
  fun uu____6013  ->
    let uu____6014 = get_smtencoding_nl_arith_repr () in
    uu____6014 = "wrapped"
let smtencoding_nl_arith_default: Prims.unit -> Prims.bool =
  fun uu____6017  ->
    let uu____6018 = get_smtencoding_nl_arith_repr () in
    uu____6018 = "boxwrap"
let smtencoding_l_arith_native: Prims.unit -> Prims.bool =
  fun uu____6021  ->
    let uu____6022 = get_smtencoding_l_arith_repr () in uu____6022 = "native"
let smtencoding_l_arith_default: Prims.unit -> Prims.bool =
  fun uu____6025  ->
    let uu____6026 = get_smtencoding_l_arith_repr () in
    uu____6026 = "boxwrap"
let split_cases: Prims.unit -> Prims.int =
  fun uu____6029  -> get_split_cases ()
let tactic_raw_binders: Prims.unit -> Prims.bool =
  fun uu____6032  -> get_tactic_raw_binders ()
let tactic_trace: Prims.unit -> Prims.bool =
  fun uu____6035  -> get_tactic_trace ()
let tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____6038  -> get_tactic_trace_d ()
let timing: Prims.unit -> Prims.bool = fun uu____6041  -> get_timing ()
let trace_error: Prims.unit -> Prims.bool =
  fun uu____6044  -> get_trace_error ()
let unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____6047  -> get_unthrottle_inductives ()
let unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____6050  -> get_unsafe_tactic_exec ()
let use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____6053  -> get_use_eq_at_higher_order ()
let use_hints: Prims.unit -> Prims.bool = fun uu____6056  -> get_use_hints ()
let use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____6059  -> get_use_hint_hashes ()
let use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____6064  -> get_use_native_tactics ()
let use_tactics: Prims.unit -> Prims.bool =
  fun uu____6067  -> get_use_tactics ()
let using_facts_from:
  Prims.unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____6076  ->
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if FStar_Util.starts_with s "-"
        then
          (let path =
             let uu____6105 =
               FStar_Util.substring_from s (Prims.parse_int "1") in
             FStar_Ident.path_of_text uu____6105 in
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
    let uu____6141 = get_using_facts_from () in
    match uu____6141 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns ->
        let uu____6173 = FStar_List.collect parse_setting ns in
        FStar_All.pipe_right uu____6173 FStar_List.rev
let warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____6212  -> get_warn_default_effects ()
let z3_exe: Prims.unit -> Prims.string =
  fun uu____6215  ->
    let uu____6216 = get_smt () in
    match uu____6216 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let z3_cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____6224  -> get_z3cliopt ()
let z3_refresh: Prims.unit -> Prims.bool =
  fun uu____6227  -> get_z3refresh ()
let z3_rlimit: Prims.unit -> Prims.int = fun uu____6230  -> get_z3rlimit ()
let z3_rlimit_factor: Prims.unit -> Prims.int =
  fun uu____6233  -> get_z3rlimit_factor ()
let z3_seed: Prims.unit -> Prims.int = fun uu____6236  -> get_z3seed ()
let use_two_phase_tc: Prims.unit -> Prims.bool =
  fun uu____6239  -> get_use_two_phase_tc ()
let no_positivity: Prims.unit -> Prims.bool =
  fun uu____6242  -> get_no_positivity ()
let ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____6245  -> get_ml_no_eta_expand_coertions ()
let warn_error: Prims.unit -> Prims.string =
  fun uu____6248  -> get_warn_error ()
let should_extract_namespace: Prims.string -> Prims.bool =
  fun m  ->
    let uu____6252 = get_extract_namespace () in
    match uu____6252 with
    | [] -> false
    | ns ->
        FStar_All.pipe_right ns
          (FStar_Util.for_some
             (fun n1  -> FStar_Util.starts_with m (FStar_String.lowercase n1)))
let should_extract_module: Prims.string -> Prims.bool =
  fun m  ->
    let uu____6265 = get_extract_module () in
    match uu____6265 with
    | [] -> false
    | l ->
        FStar_All.pipe_right l
          (FStar_Util.for_some (fun n1  -> (FStar_String.lowercase n1) = m))
let should_extract: Prims.string -> Prims.bool =
  fun m  ->
    let m1 = FStar_String.lowercase m in
    (let uu____6281 = no_extract m1 in Prims.op_Negation uu____6281) &&
      (let uu____6283 =
         let uu____6292 = get_extract_namespace () in
         let uu____6295 = get_extract_module () in (uu____6292, uu____6295) in
       match uu____6283 with
       | ([],[]) -> true
       | uu____6306 ->
           (should_extract_namespace m1) || (should_extract_module m1))
let codegen_fsharp: Prims.unit -> Prims.bool =
  fun uu____6317  ->
    let uu____6318 = codegen () in
    uu____6318 = (FStar_Pervasives_Native.Some "FSharp")