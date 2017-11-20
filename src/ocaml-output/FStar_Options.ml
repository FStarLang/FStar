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
  ("__ml_no_eta_expand_coertions", (Bool false));
  ("warn_error", (String "@1..19+20..67"))]
let init: Prims.unit -> Prims.unit =
  fun uu____1313  ->
    let o = peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let clear: Prims.unit -> Prims.unit =
  fun uu____1328  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50") in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
let _run: Prims.unit = clear ()
let get_option: Prims.string -> option_val =
  fun s  ->
    let uu____1441 =
      let uu____1444 = peek () in FStar_Util.smap_try_find uu____1444 s in
    match uu____1441 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
let lookup_opt:
  'Auu____1451 . Prims.string -> (option_val -> 'Auu____1451) -> 'Auu____1451
  = fun s  -> fun c  -> c (get_option s)
let get_admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____1467  -> lookup_opt "admit_smt_queries" as_bool
let get_admit_except:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1472  -> lookup_opt "admit_except" (as_option as_string)
let get_cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____1477  -> lookup_opt "cache_checked_modules" as_bool
let get_codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1482  -> lookup_opt "codegen" (as_option as_string)
let get_codegen_lib: Prims.unit -> Prims.string Prims.list =
  fun uu____1489  -> lookup_opt "codegen-lib" (as_list as_string)
let get_debug: Prims.unit -> Prims.string Prims.list =
  fun uu____1496  -> lookup_opt "debug" (as_list as_string)
let get_debug_level: Prims.unit -> Prims.string Prims.list =
  fun uu____1503  -> lookup_opt "debug_level" (as_list as_string)
let get_dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1510  -> lookup_opt "dep" (as_option as_string)
let get_detail_errors: Prims.unit -> Prims.bool =
  fun uu____1515  -> lookup_opt "detail_errors" as_bool
let get_detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____1518  -> lookup_opt "detail_hint_replay" as_bool
let get_doc: Prims.unit -> Prims.bool =
  fun uu____1521  -> lookup_opt "doc" as_bool
let get_dump_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1526  -> lookup_opt "dump_module" (as_list as_string)
let get_eager_inference: Prims.unit -> Prims.bool =
  fun uu____1531  -> lookup_opt "eager_inference" as_bool
let get_expose_interfaces: Prims.unit -> Prims.bool =
  fun uu____1534  -> lookup_opt "expose_interfaces" as_bool
let get_extract_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1539  -> lookup_opt "extract_module" (as_list as_string)
let get_extract_namespace: Prims.unit -> Prims.string Prims.list =
  fun uu____1546  -> lookup_opt "extract_namespace" (as_list as_string)
let get_fs_typ_app: Prims.unit -> Prims.bool =
  fun uu____1551  -> lookup_opt "fs_typ_app" as_bool
let get_fstar_home: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1556  -> lookup_opt "fstar_home" (as_option as_string)
let get_gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1563  -> lookup_opt "gen_native_tactics" (as_option as_string)
let get_hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____1568  -> lookup_opt "hide_uvar_nums" as_bool
let get_hint_info: Prims.unit -> Prims.bool =
  fun uu____1571  -> lookup_opt "hint_info" as_bool
let get_hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1576  -> lookup_opt "hint_file" (as_option as_string)
let get_in: Prims.unit -> Prims.bool =
  fun uu____1581  -> lookup_opt "in" as_bool
let get_ide: Prims.unit -> Prims.bool =
  fun uu____1584  -> lookup_opt "ide" as_bool
let get_include: Prims.unit -> Prims.string Prims.list =
  fun uu____1589  -> lookup_opt "include" (as_list as_string)
let get_indent: Prims.unit -> Prims.bool =
  fun uu____1594  -> lookup_opt "indent" as_bool
let get_initial_fuel: Prims.unit -> Prims.int =
  fun uu____1597  -> lookup_opt "initial_fuel" as_int
let get_initial_ifuel: Prims.unit -> Prims.int =
  fun uu____1600  -> lookup_opt "initial_ifuel" as_int
let get_lax: Prims.unit -> Prims.bool =
  fun uu____1603  -> lookup_opt "lax" as_bool
let get_load: Prims.unit -> Prims.string Prims.list =
  fun uu____1608  -> lookup_opt "load" (as_list as_string)
let get_log_queries: Prims.unit -> Prims.bool =
  fun uu____1613  -> lookup_opt "log_queries" as_bool
let get_log_types: Prims.unit -> Prims.bool =
  fun uu____1616  -> lookup_opt "log_types" as_bool
let get_max_fuel: Prims.unit -> Prims.int =
  fun uu____1619  -> lookup_opt "max_fuel" as_int
let get_max_ifuel: Prims.unit -> Prims.int =
  fun uu____1622  -> lookup_opt "max_ifuel" as_int
let get_min_fuel: Prims.unit -> Prims.int =
  fun uu____1625  -> lookup_opt "min_fuel" as_int
let get_MLish: Prims.unit -> Prims.bool =
  fun uu____1628  -> lookup_opt "MLish" as_bool
let get_n_cores: Prims.unit -> Prims.int =
  fun uu____1631  -> lookup_opt "n_cores" as_int
let get_no_default_includes: Prims.unit -> Prims.bool =
  fun uu____1634  -> lookup_opt "no_default_includes" as_bool
let get_no_extract: Prims.unit -> Prims.string Prims.list =
  fun uu____1639  -> lookup_opt "no_extract" (as_list as_string)
let get_no_location_info: Prims.unit -> Prims.bool =
  fun uu____1644  -> lookup_opt "no_location_info" as_bool
let get_odir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1649  -> lookup_opt "odir" (as_option as_string)
let get_ugly: Prims.unit -> Prims.bool =
  fun uu____1654  -> lookup_opt "ugly" as_bool
let get_prims: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1659  -> lookup_opt "prims" (as_option as_string)
let get_print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____1664  -> lookup_opt "print_bound_var_types" as_bool
let get_print_effect_args: Prims.unit -> Prims.bool =
  fun uu____1667  -> lookup_opt "print_effect_args" as_bool
let get_print_full_names: Prims.unit -> Prims.bool =
  fun uu____1670  -> lookup_opt "print_full_names" as_bool
let get_print_implicits: Prims.unit -> Prims.bool =
  fun uu____1673  -> lookup_opt "print_implicits" as_bool
let get_print_universes: Prims.unit -> Prims.bool =
  fun uu____1676  -> lookup_opt "print_universes" as_bool
let get_print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____1679  -> lookup_opt "print_z3_statistics" as_bool
let get_prn: Prims.unit -> Prims.bool =
  fun uu____1682  -> lookup_opt "prn" as_bool
let get_query_stats: Prims.unit -> Prims.bool =
  fun uu____1685  -> lookup_opt "query_stats" as_bool
let get_record_hints: Prims.unit -> Prims.bool =
  fun uu____1688  -> lookup_opt "record_hints" as_bool
let get_reuse_hint_for:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1693  -> lookup_opt "reuse_hint_for" (as_option as_string)
let get_silent: Prims.unit -> Prims.bool =
  fun uu____1698  -> lookup_opt "silent" as_bool
let get_smt: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1703  -> lookup_opt "smt" (as_option as_string)
let get_smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____1708  -> lookup_opt "smtencoding.elim_box" as_bool
let get_smtencoding_nl_arith_repr: Prims.unit -> Prims.string =
  fun uu____1711  -> lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr: Prims.unit -> Prims.string =
  fun uu____1714  -> lookup_opt "smtencoding.l_arith_repr" as_string
let get_split_cases: Prims.unit -> Prims.int =
  fun uu____1717  -> lookup_opt "split_cases" as_int
let get_tactic_trace: Prims.unit -> Prims.bool =
  fun uu____1720  -> lookup_opt "tactic_trace" as_bool
let get_tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____1723  -> lookup_opt "tactic_trace_d" as_int
let get_timing: Prims.unit -> Prims.bool =
  fun uu____1726  -> lookup_opt "timing" as_bool
let get_trace_error: Prims.unit -> Prims.bool =
  fun uu____1729  -> lookup_opt "trace_error" as_bool
let get_unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____1732  -> lookup_opt "unthrottle_inductives" as_bool
let get_unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____1735  -> lookup_opt "unsafe_tactic_exec" as_bool
let get_use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____1738  -> lookup_opt "use_eq_at_higher_order" as_bool
let get_use_hints: Prims.unit -> Prims.bool =
  fun uu____1741  -> lookup_opt "use_hints" as_bool
let get_use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____1744  -> lookup_opt "use_hint_hashes" as_bool
let get_use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1749  -> lookup_opt "use_native_tactics" (as_option as_string)
let get_use_tactics: Prims.unit -> Prims.bool =
  fun uu____1754  ->
    let uu____1755 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____1755
let get_using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1762  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let get_verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1773  -> lookup_opt "verify_module" (as_list as_string)
let get___temp_no_proj: Prims.unit -> Prims.string Prims.list =
  fun uu____1780  -> lookup_opt "__temp_no_proj" (as_list as_string)
let get_version: Prims.unit -> Prims.bool =
  fun uu____1785  -> lookup_opt "version" as_bool
let get_warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____1788  -> lookup_opt "warn_default_effects" as_bool
let get_z3cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____1793  -> lookup_opt "z3cliopt" (as_list as_string)
let get_z3refresh: Prims.unit -> Prims.bool =
  fun uu____1798  -> lookup_opt "z3refresh" as_bool
let get_z3rlimit: Prims.unit -> Prims.int =
  fun uu____1801  -> lookup_opt "z3rlimit" as_int
let get_z3rlimit_factor: Prims.unit -> Prims.int =
  fun uu____1804  -> lookup_opt "z3rlimit_factor" as_int
let get_z3seed: Prims.unit -> Prims.int =
  fun uu____1807  -> lookup_opt "z3seed" as_int
let get_use_two_phase_tc: Prims.unit -> Prims.bool =
  fun uu____1810  -> lookup_opt "use_two_phase_tc" as_bool
let get_no_positivity: Prims.unit -> Prims.bool =
  fun uu____1813  -> lookup_opt "__no_positivity" as_bool
let get_ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____1816  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool
let get_warn_error: Prims.unit -> Prims.string =
  fun uu____1819  -> lookup_opt "warn_error" as_string
let dlevel: Prims.string -> debug_level_t =
  fun uu___40_1822  ->
    match uu___40_1822 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let one_debug_level_geq: debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1830 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let debug_level_geq: debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____1834 = get_debug_level () in
    FStar_All.pipe_right uu____1834
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
let universe_include_path_base_dirs: Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"]
let _version: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _platform: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _compiler: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _date: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _commit: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let display_version: Prims.unit -> Prims.unit =
  fun uu____1925  ->
    let uu____1926 =
      let uu____1927 = FStar_ST.op_Bang _version in
      let uu____1974 = FStar_ST.op_Bang _platform in
      let uu____2021 = FStar_ST.op_Bang _compiler in
      let uu____2068 = FStar_ST.op_Bang _date in
      let uu____2115 = FStar_ST.op_Bang _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1927
        uu____1974 uu____2021 uu____2068 uu____2115 in
    FStar_Util.print_string uu____1926
let display_usage_aux:
  'Auu____2165 'Auu____2166 .
    ('Auu____2166,Prims.string,'Auu____2165 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2213  ->
         match uu____2213 with
         | (uu____2224,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2235 =
                      let uu____2236 = FStar_Util.colorize_bold flag in
                      FStar_Util.format1 "  --%s\n" uu____2236 in
                    FStar_Util.print_string uu____2235
                  else
                    (let uu____2238 =
                       let uu____2239 = FStar_Util.colorize_bold flag in
                       FStar_Util.format2 "  --%s  %s\n" uu____2239 doc in
                     FStar_Util.print_string uu____2238)
              | FStar_Getopt.OneArg (uu____2240,argname) ->
                  if doc = ""
                  then
                    let uu____2246 =
                      let uu____2247 = FStar_Util.colorize_bold flag in
                      let uu____2248 = FStar_Util.colorize_bold argname in
                      FStar_Util.format2 "  --%s %s\n" uu____2247 uu____2248 in
                    FStar_Util.print_string uu____2246
                  else
                    (let uu____2250 =
                       let uu____2251 = FStar_Util.colorize_bold flag in
                       let uu____2252 = FStar_Util.colorize_bold argname in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2251
                         uu____2252 doc in
                     FStar_Util.print_string uu____2250))) specs
let mk_spec:
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____2276 = o in
    match uu____2276 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2306 =
                let uu____2307 = f () in set_option name uu____2307 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2318 = f x in set_option name uu____2318 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2332 = lookup_opt name (as_option as_list') in
        FStar_Util.dflt [] uu____2332 in
      mk_list (value :: prev_values)
let reverse_accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let uu____2351 =
        let uu____2354 = lookup_opt name as_list' in
        FStar_List.append uu____2354 [value] in
      mk_list uu____2351
let accumulate_string:
  'Auu____2363 .
    Prims.string ->
      ('Auu____2363 -> Prims.string) -> 'Auu____2363 -> Prims.unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2381 =
          let uu____2382 =
            let uu____2383 = post_processor value in mk_string uu____2383 in
          accumulated_option name uu____2382 in
        set_option name uu____2381
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
    match projectee with | Const _0 -> true | uu____2461 -> false
let __proj__Const__item___0: opt_type -> option_val =
  fun projectee  -> match projectee with | Const _0 -> _0
let uu___is_IntStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2473 -> false
let __proj__IntStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | IntStr _0 -> _0
let uu___is_BoolStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2484 -> false
let uu___is_PathStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2489 -> false
let __proj__PathStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | PathStr _0 -> _0
let uu___is_SimpleStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2501 -> false
let __proj__SimpleStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0
let uu___is_EnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2515 -> false
let __proj__EnumStr__item___0: opt_type -> Prims.string Prims.list =
  fun projectee  -> match projectee with | EnumStr _0 -> _0
let uu___is_OpenEnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2539 -> false
let __proj__OpenEnumStr__item___0:
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0
let uu___is_PostProcessed: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2575 -> false
let __proj__PostProcessed__item___0:
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0
let uu___is_Accumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2605 -> false
let __proj__Accumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | Accumulated _0 -> _0
let uu___is_ReverseAccumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2617 -> false
let __proj__ReverseAccumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0
let uu___is_WithSideEffect: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2635 -> false
let __proj__WithSideEffect__item___0:
  opt_type ->
    (Prims.unit -> Prims.unit,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | WithSideEffect _0 -> _0
exception InvalidArgument of Prims.string
let uu___is_InvalidArgument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2667 -> true
    | uu____2668 -> false
let __proj__InvalidArgument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2675 -> uu____2675
let rec parse_opt_val: Prims.string -> opt_type -> Prims.string -> option_val
  =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2689 ->
              let uu____2690 = FStar_Util.safe_int_of_string str_val in
              (match uu____2690 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2694 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name) in
              mk_bool uu____2694
          | PathStr uu____2697 -> mk_path str_val
          | SimpleStr uu____2698 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2703 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2716 = parse_opt_val opt_name elem_spec str_val in
              pp uu____2716
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
            let uu____2733 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1 in
            failwith uu____2733
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
    | PostProcessed (uu____2766,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2774,elem_spec) -> desc_of_opt_type elem_spec
let rec arg_spec_of_opt_type:
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ in
      let uu____2793 = desc_of_opt_type typ in
      match uu____2793 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2799  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
let pp_validate_dir: option_val -> option_val =
  fun p  -> let pp = as_string p in FStar_Util.mkdir false pp; p
let pp_lowercase: option_val -> option_val =
  fun s  ->
    let uu____2811 =
      let uu____2812 = as_string s in FStar_String.lowercase uu____2812 in
    mk_string uu____2811
let default_warn_error: Prims.unit -> Prims.string =
  fun uu____2815  ->
    let d = FStar_Util.smap_of_list defaults in
    let uu____2819 = FStar_Util.smap_try_find d "warn_error" in
    match uu____2819 with
    | FStar_Pervasives_Native.None  ->
        failwith "default value for warn_error not found"
    | FStar_Pervasives_Native.Some s -> as_string s
let rec specs_with_types:
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun uu____2839  ->
    let uu____2850 =
      let uu____2861 =
        let uu____2872 =
          let uu____2881 = let uu____2882 = mk_bool true in Const uu____2882 in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2881,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying") in
        let uu____2883 =
          let uu____2894 =
            let uu____2905 =
              let uu____2916 =
                let uu____2927 =
                  let uu____2938 =
                    let uu____2949 =
                      let uu____2958 =
                        let uu____2959 = mk_bool true in Const uu____2959 in
                      (FStar_Getopt.noshort, "detail_errors", uu____2958,
                        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1") in
                    let uu____2960 =
                      let uu____2971 =
                        let uu____2980 =
                          let uu____2981 = mk_bool true in Const uu____2981 in
                        (FStar_Getopt.noshort, "detail_hint_replay",
                          uu____2980,
                          "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1") in
                      let uu____2982 =
                        let uu____2993 =
                          let uu____3002 =
                            let uu____3003 = mk_bool true in Const uu____3003 in
                          (FStar_Getopt.noshort, "doc", uu____3002,
                            "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.") in
                        let uu____3004 =
                          let uu____3015 =
                            let uu____3026 =
                              let uu____3035 =
                                let uu____3036 = mk_bool true in
                                Const uu____3036 in
                              (FStar_Getopt.noshort, "eager_inference",
                                uu____3035,
                                "Solve all type-inference constraints eagerly; more efficient but at the cost of generality") in
                            let uu____3037 =
                              let uu____3048 =
                                let uu____3059 =
                                  let uu____3070 =
                                    let uu____3079 =
                                      let uu____3080 = mk_bool true in
                                      Const uu____3080 in
                                    (FStar_Getopt.noshort,
                                      "expose_interfaces", uu____3079,
                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)") in
                                  let uu____3081 =
                                    let uu____3092 =
                                      let uu____3103 =
                                        let uu____3114 =
                                          let uu____3123 =
                                            let uu____3124 = mk_bool true in
                                            Const uu____3124 in
                                          (FStar_Getopt.noshort,
                                            "hide_uvar_nums", uu____3123,
                                            "Don't print unification variable numbers") in
                                        let uu____3125 =
                                          let uu____3136 =
                                            let uu____3147 =
                                              let uu____3156 =
                                                let uu____3157 = mk_bool true in
                                                Const uu____3157 in
                                              (FStar_Getopt.noshort,
                                                "hint_info", uu____3156,
                                                "Print information regarding hints (deprecated; use --query_stats instead)") in
                                            let uu____3158 =
                                              let uu____3169 =
                                                let uu____3178 =
                                                  let uu____3179 =
                                                    mk_bool true in
                                                  Const uu____3179 in
                                                (FStar_Getopt.noshort, "in",
                                                  uu____3178,
                                                  "Legacy interactive mode; reads input from stdin") in
                                              let uu____3180 =
                                                let uu____3191 =
                                                  let uu____3200 =
                                                    let uu____3201 =
                                                      mk_bool true in
                                                    Const uu____3201 in
                                                  (FStar_Getopt.noshort,
                                                    "ide", uu____3200,
                                                    "JSON-based interactive mode for IDEs") in
                                                let uu____3202 =
                                                  let uu____3213 =
                                                    let uu____3224 =
                                                      let uu____3233 =
                                                        let uu____3234 =
                                                          mk_bool true in
                                                        Const uu____3234 in
                                                      (FStar_Getopt.noshort,
                                                        "indent", uu____3233,
                                                        "Parses and outputs the files on the command line") in
                                                    let uu____3235 =
                                                      let uu____3246 =
                                                        let uu____3257 =
                                                          let uu____3268 =
                                                            let uu____3277 =
                                                              let uu____3278
                                                                =
                                                                mk_bool true in
                                                              Const
                                                                uu____3278 in
                                                            (FStar_Getopt.noshort,
                                                              "lax",
                                                              uu____3277,
                                                              "Run the lax-type checker only (admit all verification conditions)") in
                                                          let uu____3279 =
                                                            let uu____3290 =
                                                              let uu____3301
                                                                =
                                                                let uu____3310
                                                                  =
                                                                  let uu____3311
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                  Const
                                                                    uu____3311 in
                                                                (FStar_Getopt.noshort,
                                                                  "log_types",
                                                                  uu____3310,
                                                                  "Print types computed for data/val/let-bindings") in
                                                              let uu____3312
                                                                =
                                                                let uu____3323
                                                                  =
                                                                  let uu____3332
                                                                    =
                                                                    let uu____3333
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3333 in
                                                                  (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3332,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go") in
                                                                let uu____3334
                                                                  =
                                                                  let uu____3345
                                                                    =
                                                                    let uu____3356
                                                                    =
                                                                    let uu____3367
                                                                    =
                                                                    let uu____3378
                                                                    =
                                                                    let uu____3387
                                                                    =
                                                                    let uu____3388
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3388 in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3387,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)") in
                                                                    let uu____3389
                                                                    =
                                                                    let uu____3400
                                                                    =
                                                                    let uu____3411
                                                                    =
                                                                    let uu____3420
                                                                    =
                                                                    let uu____3421
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3421 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3420,
                                                                    "Ignore the default module search paths") in
                                                                    let uu____3422
                                                                    =
                                                                    let uu____3433
                                                                    =
                                                                    let uu____3444
                                                                    =
                                                                    let uu____3453
                                                                    =
                                                                    let uu____3454
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3454 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3453,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)") in
                                                                    let uu____3455
                                                                    =
                                                                    let uu____3466
                                                                    =
                                                                    let uu____3477
                                                                    =
                                                                    let uu____3488
                                                                    =
                                                                    let uu____3497
                                                                    =
                                                                    let uu____3498
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3498 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3497,
                                                                    "Print the types of bound variables") in
                                                                    let uu____3499
                                                                    =
                                                                    let uu____3510
                                                                    =
                                                                    let uu____3519
                                                                    =
                                                                    let uu____3520
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3520 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3519,
                                                                    "Print inferred predicate transformers for all computation types") in
                                                                    let uu____3521
                                                                    =
                                                                    let uu____3532
                                                                    =
                                                                    let uu____3541
                                                                    =
                                                                    let uu____3542
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3542 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3541,
                                                                    "Print full names of variables") in
                                                                    let uu____3543
                                                                    =
                                                                    let uu____3554
                                                                    =
                                                                    let uu____3563
                                                                    =
                                                                    let uu____3564
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3564 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3563,
                                                                    "Print implicit arguments") in
                                                                    let uu____3565
                                                                    =
                                                                    let uu____3576
                                                                    =
                                                                    let uu____3585
                                                                    =
                                                                    let uu____3586
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3586 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3585,
                                                                    "Print universes") in
                                                                    let uu____3587
                                                                    =
                                                                    let uu____3598
                                                                    =
                                                                    let uu____3607
                                                                    =
                                                                    let uu____3608
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3608 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3607,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)") in
                                                                    let uu____3609
                                                                    =
                                                                    let uu____3620
                                                                    =
                                                                    let uu____3629
                                                                    =
                                                                    let uu____3630
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3630 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3629,
                                                                    "Print full names (deprecated; use --print_full_names instead)") in
                                                                    let uu____3631
                                                                    =
                                                                    let uu____3642
                                                                    =
                                                                    let uu____3651
                                                                    =
                                                                    let uu____3652
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3652 in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3651,
                                                                    "Print SMT query statistics") in
                                                                    let uu____3653
                                                                    =
                                                                    let uu____3664
                                                                    =
                                                                    let uu____3673
                                                                    =
                                                                    let uu____3674
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3674 in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3673,
                                                                    "Record a database of hints for efficient proof replay") in
                                                                    let uu____3675
                                                                    =
                                                                    let uu____3686
                                                                    =
                                                                    let uu____3697
                                                                    =
                                                                    let uu____3706
                                                                    =
                                                                    let uu____3707
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3707 in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3706,
                                                                    " ") in
                                                                    let uu____3708
                                                                    =
                                                                    let uu____3719
                                                                    =
                                                                    let uu____3730
                                                                    =
                                                                    let uu____3741
                                                                    =
                                                                    let uu____3752
                                                                    =
                                                                    let uu____3763
                                                                    =
                                                                    let uu____3774
                                                                    =
                                                                    let uu____3783
                                                                    =
                                                                    let uu____3784
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3784 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3783,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)") in
                                                                    let uu____3785
                                                                    =
                                                                    let uu____3796
                                                                    =
                                                                    let uu____3807
                                                                    =
                                                                    let uu____3816
                                                                    =
                                                                    let uu____3817
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3817 in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3816,
                                                                    "Print the time it takes to verify each top-level definition") in
                                                                    let uu____3818
                                                                    =
                                                                    let uu____3829
                                                                    =
                                                                    let uu____3838
                                                                    =
                                                                    let uu____3839
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3839 in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3838,
                                                                    "Don't print an error message; show an exception trace instead") in
                                                                    let uu____3840
                                                                    =
                                                                    let uu____3851
                                                                    =
                                                                    let uu____3860
                                                                    =
                                                                    let uu____3861
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3861 in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3860,
                                                                    "Emit output formatted for debugging") in
                                                                    let uu____3862
                                                                    =
                                                                    let uu____3873
                                                                    =
                                                                    let uu____3882
                                                                    =
                                                                    let uu____3883
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3883 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____3882,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)") in
                                                                    let uu____3884
                                                                    =
                                                                    let uu____3895
                                                                    =
                                                                    let uu____3904
                                                                    =
                                                                    let uu____3905
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3905 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____3904,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.") in
                                                                    let uu____3906
                                                                    =
                                                                    let uu____3917
                                                                    =
                                                                    let uu____3926
                                                                    =
                                                                    let uu____3927
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3927 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____3926,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)") in
                                                                    let uu____3928
                                                                    =
                                                                    let uu____3939
                                                                    =
                                                                    let uu____3948
                                                                    =
                                                                    let uu____3949
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3949 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____3948,
                                                                    "Use a previously recorded hints database for proof replay") in
                                                                    let uu____3950
                                                                    =
                                                                    let uu____3961
                                                                    =
                                                                    let uu____3970
                                                                    =
                                                                    let uu____3971
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3971 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____3970,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database") in
                                                                    let uu____3972
                                                                    =
                                                                    let uu____3983
                                                                    =
                                                                    let uu____3994
                                                                    =
                                                                    let uu____4003
                                                                    =
                                                                    let uu____4004
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4004 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4003,
                                                                    "Do not run the tactic engine before discharging a VC") in
                                                                    let uu____4005
                                                                    =
                                                                    let uu____4016
                                                                    =
                                                                    let uu____4027
                                                                    =
                                                                    let uu____4038
                                                                    =
                                                                    let uu____4048
                                                                    =
                                                                    let uu____4049
                                                                    =
                                                                    let uu____4056
                                                                    =
                                                                    let uu____4057
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4057 in
                                                                    ((fun
                                                                    uu____4062
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____4056) in
                                                                    WithSideEffect
                                                                    uu____4049 in
                                                                    (118,
                                                                    "version",
                                                                    uu____4048,
                                                                    "Display version number") in
                                                                    let uu____4066
                                                                    =
                                                                    let uu____4078
                                                                    =
                                                                    let uu____4087
                                                                    =
                                                                    let uu____4088
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4088 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4087,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)") in
                                                                    let uu____4089
                                                                    =
                                                                    let uu____4100
                                                                    =
                                                                    let uu____4111
                                                                    =
                                                                    let uu____4120
                                                                    =
                                                                    let uu____4121
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4121 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4120,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness") in
                                                                    let uu____4122
                                                                    =
                                                                    let uu____4133
                                                                    =
                                                                    let uu____4144
                                                                    =
                                                                    let uu____4155
                                                                    =
                                                                    let uu____4166
                                                                    =
                                                                    let uu____4175
                                                                    =
                                                                    let uu____4176
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4176 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    uu____4175,
                                                                    "Use the two phase typechecker") in
                                                                    let uu____4177
                                                                    =
                                                                    let uu____4188
                                                                    =
                                                                    let uu____4197
                                                                    =
                                                                    let uu____4198
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4198 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4197,
                                                                    "Don't check positivity of inductive types") in
                                                                    let uu____4199
                                                                    =
                                                                    let uu____4210
                                                                    =
                                                                    let uu____4219
                                                                    =
                                                                    let uu____4220
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4220 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4219,
                                                                    "Do not eta-expand coertions in generated OCaml") in
                                                                    let uu____4221
                                                                    =
                                                                    let uu____4232
                                                                    =
                                                                    let uu____4241
                                                                    =
                                                                    let uu____4242
                                                                    =
                                                                    default_warn_error
                                                                    () in
                                                                    Prims.strcat
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.\n\t\tThe default is"
                                                                    uu____4242 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    uu____4241) in
                                                                    let uu____4243
                                                                    =
                                                                    let uu____4254
                                                                    =
                                                                    let uu____4264
                                                                    =
                                                                    let uu____4265
                                                                    =
                                                                    let uu____4272
                                                                    =
                                                                    let uu____4273
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4273 in
                                                                    ((fun
                                                                    uu____4278
                                                                     ->
                                                                    (
                                                                    let uu____4280
                                                                    =
                                                                    specs () in
                                                                    display_usage_aux
                                                                    uu____4280);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____4272) in
                                                                    WithSideEffect
                                                                    uu____4265 in
                                                                    (104,
                                                                    "help",
                                                                    uu____4264,
                                                                    "Display this information") in
                                                                    [uu____4254] in
                                                                    uu____4232
                                                                    ::
                                                                    uu____4243 in
                                                                    uu____4210
                                                                    ::
                                                                    uu____4221 in
                                                                    uu____4188
                                                                    ::
                                                                    uu____4199 in
                                                                    uu____4166
                                                                    ::
                                                                    uu____4177 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4155 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4144 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4133 in
                                                                    uu____4111
                                                                    ::
                                                                    uu____4122 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4100 in
                                                                    uu____4078
                                                                    ::
                                                                    uu____4089 in
                                                                    uu____4038
                                                                    ::
                                                                    uu____4066 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4027 in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4016 in
                                                                    uu____3994
                                                                    ::
                                                                    uu____4005 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____3983 in
                                                                    uu____3961
                                                                    ::
                                                                    uu____3972 in
                                                                    uu____3939
                                                                    ::
                                                                    uu____3950 in
                                                                    uu____3917
                                                                    ::
                                                                    uu____3928 in
                                                                    uu____3895
                                                                    ::
                                                                    uu____3906 in
                                                                    uu____3873
                                                                    ::
                                                                    uu____3884 in
                                                                    uu____3851
                                                                    ::
                                                                    uu____3862 in
                                                                    uu____3829
                                                                    ::
                                                                    uu____3840 in
                                                                    uu____3807
                                                                    ::
                                                                    uu____3818 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3796 in
                                                                    uu____3774
                                                                    ::
                                                                    uu____3785 in
                                                                    (FStar_Getopt.noshort,
                                                                    "split_cases",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Partition VC of a match into groups of <positive_integer> cases")
                                                                    ::
                                                                    uu____3763 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3752 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3741 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3730 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3719 in
                                                                    uu____3697
                                                                    ::
                                                                    uu____3708 in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3686 in
                                                                    uu____3664
                                                                    ::
                                                                    uu____3675 in
                                                                    uu____3642
                                                                    ::
                                                                    uu____3653 in
                                                                    uu____3620
                                                                    ::
                                                                    uu____3631 in
                                                                    uu____3598
                                                                    ::
                                                                    uu____3609 in
                                                                    uu____3576
                                                                    ::
                                                                    uu____3587 in
                                                                    uu____3554
                                                                    ::
                                                                    uu____3565 in
                                                                    uu____3532
                                                                    ::
                                                                    uu____3543 in
                                                                    uu____3510
                                                                    ::
                                                                    uu____3521 in
                                                                    uu____3488
                                                                    ::
                                                                    uu____3499 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3477 in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3466 in
                                                                    uu____3444
                                                                    ::
                                                                    uu____3455 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Do not extract code from this module")
                                                                    ::
                                                                    uu____3433 in
                                                                    uu____3411
                                                                    ::
                                                                    uu____3422 in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3400 in
                                                                    uu____3378
                                                                    ::
                                                                    uu____3389 in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3367 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3356 in
                                                                  (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (
                                                                    IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3345 in
                                                                uu____3323 ::
                                                                  uu____3334 in
                                                              uu____3301 ::
                                                                uu____3312 in
                                                            (FStar_Getopt.noshort,
                                                              "load",
                                                              (ReverseAccumulated
                                                                 (PathStr
                                                                    "module")),
                                                              "Load compiled module")
                                                              :: uu____3290 in
                                                          uu____3268 ::
                                                            uu____3279 in
                                                        (FStar_Getopt.noshort,
                                                          "initial_ifuel",
                                                          (IntStr
                                                             "non-negative integer"),
                                                          "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                          :: uu____3257 in
                                                      (FStar_Getopt.noshort,
                                                        "initial_fuel",
                                                        (IntStr
                                                           "non-negative integer"),
                                                        "Number of unrolling of recursive functions to try initially (default 2)")
                                                        :: uu____3246 in
                                                    uu____3224 :: uu____3235 in
                                                  (FStar_Getopt.noshort,
                                                    "include",
                                                    (ReverseAccumulated
                                                       (PathStr "path")),
                                                    "A directory in which to search for files included on the command line")
                                                    :: uu____3213 in
                                                uu____3191 :: uu____3202 in
                                              uu____3169 :: uu____3180 in
                                            uu____3147 :: uu____3158 in
                                          (FStar_Getopt.noshort, "hint_file",
                                            (PathStr "path"),
                                            "Read/write hints to <path> (instead of module-specific hints files)")
                                            :: uu____3136 in
                                        uu____3114 :: uu____3125 in
                                      (FStar_Getopt.noshort,
                                        "gen_native_tactics",
                                        (PathStr "[path]"),
                                        "Compile all user tactics used in the module in <path>")
                                        :: uu____3103 in
                                    (FStar_Getopt.noshort, "fstar_home",
                                      (PathStr "dir"),
                                      "Set the FSTAR_HOME variable to <dir>")
                                      :: uu____3092 in
                                  uu____3070 :: uu____3081 in
                                (FStar_Getopt.noshort, "extract_namespace",
                                  (Accumulated
                                     (PostProcessed
                                        (pp_lowercase,
                                          (SimpleStr "namespace name")))),
                                  "Only extract modules in the specified namespace")
                                  :: uu____3059 in
                              (FStar_Getopt.noshort, "extract_module",
                                (Accumulated
                                   (PostProcessed
                                      (pp_lowercase,
                                        (SimpleStr "module_name")))),
                                "Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                :: uu____3048 in
                            uu____3026 :: uu____3037 in
                          (FStar_Getopt.noshort, "dump_module",
                            (Accumulated (SimpleStr "module_name")), "") ::
                            uu____3015 in
                        uu____2993 :: uu____3004 in
                      uu____2971 :: uu____2982 in
                    uu____2949 :: uu____2960 in
                  (FStar_Getopt.noshort, "dep",
                    (EnumStr ["make"; "graph"; "full"]),
                    "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                    :: uu____2938 in
                (FStar_Getopt.noshort, "debug_level",
                  (Accumulated
                     (OpenEnumStr
                        (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                  "Control the verbosity of debugging info") :: uu____2927 in
              (FStar_Getopt.noshort, "debug",
                (Accumulated (SimpleStr "module_name")),
                "Print lots of debugging information while checking module")
                :: uu____2916 in
            (FStar_Getopt.noshort, "codegen-lib",
              (Accumulated (SimpleStr "namespace")),
              "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
              :: uu____2905 in
          (FStar_Getopt.noshort, "codegen",
            (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "tactics"]),
            "Generate code for execution") :: uu____2894 in
        uu____2872 :: uu____2883 in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2861 in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2850
and specs: Prims.unit -> FStar_Getopt.opt Prims.list =
  fun uu____4978  ->
    let uu____4981 = specs_with_types () in
    FStar_List.map
      (fun uu____5006  ->
         match uu____5006 with
         | (short,long,typ,doc) ->
             let uu____5019 =
               let uu____5030 = arg_spec_of_opt_type long typ in
               (short, long, uu____5030, doc) in
             mk_spec uu____5019) uu____4981
let settable: Prims.string -> Prims.bool =
  fun uu___41_5037  ->
    match uu___41_5037 with
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
    | "warn_error" -> true
    | "z3rlimit_factor" -> true
    | "z3rlimit" -> true
    | "z3refresh" -> true
    | "use_two_phase_tc" -> true
    | uu____5038 -> false
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
       (fun uu____5095  ->
          match uu____5095 with
          | (uu____5106,x,uu____5108,uu____5109) -> settable x))
let resettable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5155  ->
          match uu____5155 with
          | (uu____5166,x,uu____5168,uu____5169) -> resettable x))
let display_usage: Prims.unit -> Prims.unit =
  fun uu____5176  ->
    let uu____5177 = specs () in display_usage_aux uu____5177
let fstar_home: Prims.unit -> Prims.string =
  fun uu____5192  ->
    let uu____5193 = get_fstar_home () in
    match uu____5193 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        ((let uu____5199 =
            let uu____5204 = mk_string x1 in ("fstar_home", uu____5204) in
          set_option' uu____5199);
         x1)
    | FStar_Pervasives_Native.Some x -> x
exception File_argument of Prims.string
let uu___is_File_argument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____5212 -> true
    | uu____5213 -> false
let __proj__File_argument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____5220 -> uu____5220
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
          let uu____5264 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____5264
let file_list_: Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let parse_cmd_line:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____5286  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5291 =
             let uu____5294 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____5294 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____5291) in
    let uu____5397 =
      let uu____5400 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5400 in
    (res, uu____5397)
let file_list: Prims.unit -> Prims.string Prims.list =
  fun uu____5459  -> FStar_ST.op_Bang file_list_
let restore_cmd_line_options: Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____5519 = specs () in
       FStar_Getopt.parse_cmdline uu____5519 (fun x  -> ()) in
     (let uu____5525 =
        let uu____5530 =
          let uu____5531 = FStar_List.map mk_string old_verify_module in
          List uu____5531 in
        ("verify_module", uu____5530) in
      set_option' uu____5525);
     r)
let module_name_of_file_name: Prims.string -> Prims.string =
  fun f  ->
    let f1 = FStar_Util.basename f in
    let f2 =
      let uu____5539 =
        let uu____5540 =
          let uu____5541 =
            let uu____5542 = FStar_Util.get_file_extension f1 in
            FStar_String.length uu____5542 in
          (FStar_String.length f1) - uu____5541 in
        uu____5540 - (Prims.parse_int "1") in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5539 in
    FStar_String.lowercase f2
let should_verify: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5546 = get_lax () in
    if uu____5546
    then false
    else
      (let l = get_verify_module () in
       FStar_List.contains (FStar_String.lowercase m) l)
let should_verify_file: Prims.string -> Prims.bool =
  fun fn  ->
    let uu____5554 = module_name_of_file_name fn in should_verify uu____5554
let dont_gen_projectors: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5558 = get___temp_no_proj () in
    FStar_List.contains m uu____5558
let should_print_message: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5564 = should_verify m in
    if uu____5564 then m <> "Prims" else false
let include_path: Prims.unit -> Prims.string Prims.list =
  fun uu____5570  ->
    let uu____5571 = get_no_default_includes () in
    if uu____5571
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____5579 =
         let uu____5582 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____5582
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____5595 =
         let uu____5598 = get_include () in
         FStar_List.append uu____5598 ["."] in
       FStar_List.append uu____5579 uu____5595)
let find_file: Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____5606 = FStar_Util.is_path_absolute filename in
    if uu____5606
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5613 =
         let uu____5616 = include_path () in FStar_List.rev uu____5616 in
       FStar_Util.find_map uu____5613
         (fun p  ->
            let path = FStar_Util.join_paths p filename in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
let prims: Prims.unit -> Prims.string =
  fun uu____5628  ->
    let uu____5629 = get_prims () in
    match uu____5629 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst" in
        let uu____5633 = find_file filename in
        (match uu____5633 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5637 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename in
             failwith uu____5637)
    | FStar_Pervasives_Native.Some x -> x
let prims_basename: Prims.unit -> Prims.string =
  fun uu____5641  ->
    let uu____5642 = prims () in FStar_Util.basename uu____5642
let pervasives: Prims.unit -> Prims.string =
  fun uu____5645  ->
    let filename = "FStar.Pervasives.fst" in
    let uu____5647 = find_file filename in
    match uu____5647 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5651 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5651
let pervasives_basename: Prims.unit -> Prims.string =
  fun uu____5654  ->
    let uu____5655 = pervasives () in FStar_Util.basename uu____5655
let pervasives_native_basename: Prims.unit -> Prims.string =
  fun uu____5658  ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____5660 = find_file filename in
    match uu____5660 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5664 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5664
let prepend_output_dir: Prims.string -> Prims.string =
  fun fname  ->
    let uu____5668 = get_odir () in
    match uu____5668 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
let __temp_no_proj: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5675 = get___temp_no_proj () in
    FStar_All.pipe_right uu____5675 (FStar_List.contains s)
let admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____5682  -> get_admit_smt_queries ()
let admit_except: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5687  -> get_admit_except ()
let cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____5690  -> get_cache_checked_modules ()
let codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5695  -> get_codegen ()
let codegen_libs: Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____5702  ->
    let uu____5703 = get_codegen_lib () in
    FStar_All.pipe_right uu____5703
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
let debug_any: Prims.unit -> Prims.bool =
  fun uu____5718  -> let uu____5719 = get_debug () in uu____5719 <> []
let debug_at_level: Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      (let uu____5732 = get_debug () in
       FStar_All.pipe_right uu____5732 (FStar_List.contains modul)) &&
        (debug_level_geq level)
let dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5741  -> get_dep ()
let detail_errors: Prims.unit -> Prims.bool =
  fun uu____5744  -> get_detail_errors ()
let detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____5747  -> get_detail_hint_replay ()
let doc: Prims.unit -> Prims.bool = fun uu____5750  -> get_doc ()
let dump_module: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5754 = get_dump_module () in
    FStar_All.pipe_right uu____5754 (FStar_List.contains s)
let eager_inference: Prims.unit -> Prims.bool =
  fun uu____5761  -> get_eager_inference ()
let expose_interfaces: Prims.unit -> Prims.bool =
  fun uu____5764  -> get_expose_interfaces ()
let fs_typ_app: Prims.string -> Prims.bool =
  fun filename  ->
    let uu____5768 = FStar_ST.op_Bang light_off_files in
    FStar_List.contains filename uu____5768
let gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5825  -> get_gen_native_tactics ()
let full_context_dependency: Prims.unit -> Prims.bool =
  fun uu____5828  -> true
let hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____5831  -> get_hide_uvar_nums ()
let hint_info: Prims.unit -> Prims.bool =
  fun uu____5834  -> (get_hint_info ()) || (get_query_stats ())
let hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5839  -> get_hint_file ()
let ide: Prims.unit -> Prims.bool = fun uu____5842  -> get_ide ()
let indent: Prims.unit -> Prims.bool = fun uu____5845  -> get_indent ()
let initial_fuel: Prims.unit -> Prims.int =
  fun uu____5848  ->
    let uu____5849 = get_initial_fuel () in
    let uu____5850 = get_max_fuel () in Prims.min uu____5849 uu____5850
let initial_ifuel: Prims.unit -> Prims.int =
  fun uu____5853  ->
    let uu____5854 = get_initial_ifuel () in
    let uu____5855 = get_max_ifuel () in Prims.min uu____5854 uu____5855
let interactive: Prims.unit -> Prims.bool =
  fun uu____5858  -> (get_in ()) || (get_ide ())
let lax: Prims.unit -> Prims.bool = fun uu____5861  -> get_lax ()
let load: Prims.unit -> Prims.string Prims.list =
  fun uu____5866  -> get_load ()
let legacy_interactive: Prims.unit -> Prims.bool =
  fun uu____5869  -> get_in ()
let log_queries: Prims.unit -> Prims.bool =
  fun uu____5872  -> get_log_queries ()
let log_types: Prims.unit -> Prims.bool = fun uu____5875  -> get_log_types ()
let max_fuel: Prims.unit -> Prims.int = fun uu____5878  -> get_max_fuel ()
let max_ifuel: Prims.unit -> Prims.int = fun uu____5881  -> get_max_ifuel ()
let min_fuel: Prims.unit -> Prims.int = fun uu____5884  -> get_min_fuel ()
let ml_ish: Prims.unit -> Prims.bool = fun uu____5887  -> get_MLish ()
let set_ml_ish: Prims.unit -> Prims.unit =
  fun uu____5890  -> set_option "MLish" (Bool true)
let n_cores: Prims.unit -> Prims.int = fun uu____5893  -> get_n_cores ()
let no_default_includes: Prims.unit -> Prims.bool =
  fun uu____5896  -> get_no_default_includes ()
let no_extract: Prims.string -> Prims.bool =
  fun s  ->
    let s1 = FStar_String.lowercase s in
    let uu____5901 = get_no_extract () in
    FStar_All.pipe_right uu____5901
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
let no_location_info: Prims.unit -> Prims.bool =
  fun uu____5910  -> get_no_location_info ()
let output_dir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5915  -> get_odir ()
let ugly: Prims.unit -> Prims.bool = fun uu____5918  -> get_ugly ()
let print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____5921  -> get_print_bound_var_types ()
let print_effect_args: Prims.unit -> Prims.bool =
  fun uu____5924  -> get_print_effect_args ()
let print_implicits: Prims.unit -> Prims.bool =
  fun uu____5927  -> get_print_implicits ()
let print_real_names: Prims.unit -> Prims.bool =
  fun uu____5930  -> (get_prn ()) || (get_print_full_names ())
let print_universes: Prims.unit -> Prims.bool =
  fun uu____5933  -> get_print_universes ()
let print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____5936  -> (get_print_z3_statistics ()) || (get_query_stats ())
let query_stats: Prims.unit -> Prims.bool =
  fun uu____5939  -> get_query_stats ()
let record_hints: Prims.unit -> Prims.bool =
  fun uu____5942  -> get_record_hints ()
let reuse_hint_for: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____5947  -> get_reuse_hint_for ()
let silent: Prims.unit -> Prims.bool = fun uu____5950  -> get_silent ()
let smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____5953  -> get_smtencoding_elim_box ()
let smtencoding_nl_arith_native: Prims.unit -> Prims.bool =
  fun uu____5956  ->
    let uu____5957 = get_smtencoding_nl_arith_repr () in
    uu____5957 = "native"
let smtencoding_nl_arith_wrapped: Prims.unit -> Prims.bool =
  fun uu____5960  ->
    let uu____5961 = get_smtencoding_nl_arith_repr () in
    uu____5961 = "wrapped"
let smtencoding_nl_arith_default: Prims.unit -> Prims.bool =
  fun uu____5964  ->
    let uu____5965 = get_smtencoding_nl_arith_repr () in
    uu____5965 = "boxwrap"
let smtencoding_l_arith_native: Prims.unit -> Prims.bool =
  fun uu____5968  ->
    let uu____5969 = get_smtencoding_l_arith_repr () in uu____5969 = "native"
let smtencoding_l_arith_default: Prims.unit -> Prims.bool =
  fun uu____5972  ->
    let uu____5973 = get_smtencoding_l_arith_repr () in
    uu____5973 = "boxwrap"
let split_cases: Prims.unit -> Prims.int =
  fun uu____5976  -> get_split_cases ()
let tactic_trace: Prims.unit -> Prims.bool =
  fun uu____5979  -> get_tactic_trace ()
let tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____5982  -> get_tactic_trace_d ()
let timing: Prims.unit -> Prims.bool = fun uu____5985  -> get_timing ()
let trace_error: Prims.unit -> Prims.bool =
  fun uu____5988  -> get_trace_error ()
let unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____5991  -> get_unthrottle_inductives ()
let unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____5994  -> get_unsafe_tactic_exec ()
let use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____5997  -> get_use_eq_at_higher_order ()
let use_hints: Prims.unit -> Prims.bool = fun uu____6000  -> get_use_hints ()
let use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____6003  -> get_use_hint_hashes ()
let use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____6008  -> get_use_native_tactics ()
let use_tactics: Prims.unit -> Prims.bool =
  fun uu____6011  -> get_use_tactics ()
let using_facts_from:
  Prims.unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____6020  ->
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if FStar_Util.starts_with s "-"
        then
          (let path =
             let uu____6049 =
               FStar_Util.substring_from s (Prims.parse_int "1") in
             FStar_Ident.path_of_text uu____6049 in
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
    let uu____6085 = get_using_facts_from () in
    match uu____6085 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns ->
        let uu____6117 = FStar_List.collect parse_setting ns in
        FStar_All.pipe_right uu____6117 FStar_List.rev
let warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____6156  -> get_warn_default_effects ()
let z3_exe: Prims.unit -> Prims.string =
  fun uu____6159  ->
    let uu____6160 = get_smt () in
    match uu____6160 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let z3_cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____6168  -> get_z3cliopt ()
let z3_refresh: Prims.unit -> Prims.bool =
  fun uu____6171  -> get_z3refresh ()
let z3_rlimit: Prims.unit -> Prims.int = fun uu____6174  -> get_z3rlimit ()
let z3_rlimit_factor: Prims.unit -> Prims.int =
  fun uu____6177  -> get_z3rlimit_factor ()
let z3_seed: Prims.unit -> Prims.int = fun uu____6180  -> get_z3seed ()
let use_two_phase_tc: Prims.unit -> Prims.bool =
  fun uu____6183  -> get_use_two_phase_tc ()
let no_positivity: Prims.unit -> Prims.bool =
  fun uu____6186  -> get_no_positivity ()
let ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____6189  -> get_ml_no_eta_expand_coertions ()
let warn_error: Prims.unit -> Prims.string =
  fun uu____6192  -> get_warn_error ()
let should_extract_namespace: Prims.string -> Prims.bool =
  fun m  ->
    let uu____6196 = get_extract_namespace () in
    match uu____6196 with
    | [] -> false
    | ns ->
        FStar_All.pipe_right ns
          (FStar_Util.for_some
             (fun n1  -> FStar_Util.starts_with m (FStar_String.lowercase n1)))
let should_extract_module: Prims.string -> Prims.bool =
  fun m  ->
    let uu____6209 = get_extract_module () in
    match uu____6209 with
    | [] -> false
    | l ->
        FStar_All.pipe_right l
          (FStar_Util.for_some (fun n1  -> (FStar_String.lowercase n1) = m))
let should_extract: Prims.string -> Prims.bool =
  fun m  ->
    let m1 = FStar_String.lowercase m in
    (let uu____6225 = no_extract m1 in Prims.op_Negation uu____6225) &&
      (let uu____6227 =
         let uu____6236 = get_extract_namespace () in
         let uu____6239 = get_extract_module () in (uu____6236, uu____6239) in
       match uu____6227 with
       | ([],[]) -> true
       | uu____6250 ->
           (should_extract_namespace m1) || (should_extract_module m1))
let codegen_fsharp: Prims.unit -> Prims.bool =
  fun uu____6261  ->
    let uu____6262 = codegen () in
    uu____6262 = (FStar_Pervasives_Native.Some "FSharp")