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
  fun uu___59_309  ->
    match uu___59_309 with
    | Bool b -> b
    | uu____311 -> failwith "Impos: expected Bool"
let as_int: option_val -> Prims.int =
  fun uu___60_314  ->
    match uu___60_314 with
    | Int b -> b
    | uu____316 -> failwith "Impos: expected Int"
let as_string: option_val -> Prims.string =
  fun uu___61_319  ->
    match uu___61_319 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____322 -> failwith "Impos: expected String"
let as_list': option_val -> option_val Prims.list =
  fun uu___62_327  ->
    match uu___62_327 with
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
    fun uu___63_378  ->
      match uu___63_378 with
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
  ("explicit_deps", (Bool false));
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
  ("verify", (Bool true));
  ("verify_all", (Bool false));
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
let get_explicit_deps: Prims.unit -> Prims.bool =
  fun uu____1534  -> lookup_opt "explicit_deps" as_bool
let get_extract_all: Prims.unit -> Prims.bool =
  fun uu____1537  -> lookup_opt "extract_all" as_bool
let get_extract_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1542  -> lookup_opt "extract_module" (as_list as_string)
let get_extract_namespace: Prims.unit -> Prims.string Prims.list =
  fun uu____1549  -> lookup_opt "extract_namespace" (as_list as_string)
let get_fs_typ_app: Prims.unit -> Prims.bool =
  fun uu____1554  -> lookup_opt "fs_typ_app" as_bool
let get_fstar_home: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1559  -> lookup_opt "fstar_home" (as_option as_string)
let get_gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1566  -> lookup_opt "gen_native_tactics" (as_option as_string)
let get_hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____1571  -> lookup_opt "hide_uvar_nums" as_bool
let get_hint_info: Prims.unit -> Prims.bool =
  fun uu____1574  -> lookup_opt "hint_info" as_bool
let get_hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1579  -> lookup_opt "hint_file" (as_option as_string)
let get_in: Prims.unit -> Prims.bool =
  fun uu____1584  -> lookup_opt "in" as_bool
let get_ide: Prims.unit -> Prims.bool =
  fun uu____1587  -> lookup_opt "ide" as_bool
let get_include: Prims.unit -> Prims.string Prims.list =
  fun uu____1592  -> lookup_opt "include" (as_list as_string)
let get_indent: Prims.unit -> Prims.bool =
  fun uu____1597  -> lookup_opt "indent" as_bool
let get_initial_fuel: Prims.unit -> Prims.int =
  fun uu____1600  -> lookup_opt "initial_fuel" as_int
let get_initial_ifuel: Prims.unit -> Prims.int =
  fun uu____1603  -> lookup_opt "initial_ifuel" as_int
let get_lax: Prims.unit -> Prims.bool =
  fun uu____1606  -> lookup_opt "lax" as_bool
let get_load: Prims.unit -> Prims.string Prims.list =
  fun uu____1611  -> lookup_opt "load" (as_list as_string)
let get_log_queries: Prims.unit -> Prims.bool =
  fun uu____1616  -> lookup_opt "log_queries" as_bool
let get_log_types: Prims.unit -> Prims.bool =
  fun uu____1619  -> lookup_opt "log_types" as_bool
let get_max_fuel: Prims.unit -> Prims.int =
  fun uu____1622  -> lookup_opt "max_fuel" as_int
let get_max_ifuel: Prims.unit -> Prims.int =
  fun uu____1625  -> lookup_opt "max_ifuel" as_int
let get_min_fuel: Prims.unit -> Prims.int =
  fun uu____1628  -> lookup_opt "min_fuel" as_int
let get_MLish: Prims.unit -> Prims.bool =
  fun uu____1631  -> lookup_opt "MLish" as_bool
let get_n_cores: Prims.unit -> Prims.int =
  fun uu____1634  -> lookup_opt "n_cores" as_int
let get_no_default_includes: Prims.unit -> Prims.bool =
  fun uu____1637  -> lookup_opt "no_default_includes" as_bool
let get_no_extract: Prims.unit -> Prims.string Prims.list =
  fun uu____1642  -> lookup_opt "no_extract" (as_list as_string)
let get_no_location_info: Prims.unit -> Prims.bool =
  fun uu____1647  -> lookup_opt "no_location_info" as_bool
let get_odir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1652  -> lookup_opt "odir" (as_option as_string)
let get_ugly: Prims.unit -> Prims.bool =
  fun uu____1657  -> lookup_opt "ugly" as_bool
let get_prims: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1662  -> lookup_opt "prims" (as_option as_string)
let get_print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____1667  -> lookup_opt "print_bound_var_types" as_bool
let get_print_effect_args: Prims.unit -> Prims.bool =
  fun uu____1670  -> lookup_opt "print_effect_args" as_bool
let get_print_full_names: Prims.unit -> Prims.bool =
  fun uu____1673  -> lookup_opt "print_full_names" as_bool
let get_print_implicits: Prims.unit -> Prims.bool =
  fun uu____1676  -> lookup_opt "print_implicits" as_bool
let get_print_universes: Prims.unit -> Prims.bool =
  fun uu____1679  -> lookup_opt "print_universes" as_bool
let get_print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____1682  -> lookup_opt "print_z3_statistics" as_bool
let get_prn: Prims.unit -> Prims.bool =
  fun uu____1685  -> lookup_opt "prn" as_bool
let get_query_stats: Prims.unit -> Prims.bool =
  fun uu____1688  -> lookup_opt "query_stats" as_bool
let get_record_hints: Prims.unit -> Prims.bool =
  fun uu____1691  -> lookup_opt "record_hints" as_bool
let get_reuse_hint_for:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1696  -> lookup_opt "reuse_hint_for" (as_option as_string)
let get_silent: Prims.unit -> Prims.bool =
  fun uu____1701  -> lookup_opt "silent" as_bool
let get_smt: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1706  -> lookup_opt "smt" (as_option as_string)
let get_smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____1711  -> lookup_opt "smtencoding.elim_box" as_bool
let get_smtencoding_nl_arith_repr: Prims.unit -> Prims.string =
  fun uu____1714  -> lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr: Prims.unit -> Prims.string =
  fun uu____1717  -> lookup_opt "smtencoding.l_arith_repr" as_string
let get_split_cases: Prims.unit -> Prims.int =
  fun uu____1720  -> lookup_opt "split_cases" as_int
let get_tactic_trace: Prims.unit -> Prims.bool =
  fun uu____1723  -> lookup_opt "tactic_trace" as_bool
let get_tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____1726  -> lookup_opt "tactic_trace_d" as_int
let get_timing: Prims.unit -> Prims.bool =
  fun uu____1729  -> lookup_opt "timing" as_bool
let get_trace_error: Prims.unit -> Prims.bool =
  fun uu____1732  -> lookup_opt "trace_error" as_bool
let get_unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____1735  -> lookup_opt "unthrottle_inductives" as_bool
let get_unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____1738  -> lookup_opt "unsafe_tactic_exec" as_bool
let get_use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____1741  -> lookup_opt "use_eq_at_higher_order" as_bool
let get_use_hints: Prims.unit -> Prims.bool =
  fun uu____1744  -> lookup_opt "use_hints" as_bool
let get_use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____1747  -> lookup_opt "use_hint_hashes" as_bool
let get_use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1752  -> lookup_opt "use_native_tactics" (as_option as_string)
let get_use_tactics: Prims.unit -> Prims.bool =
  fun uu____1757  ->
    let uu____1758 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____1758
let get_using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1765  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let get_verify_all: Prims.unit -> Prims.bool =
  fun uu____1774  -> lookup_opt "verify_all" as_bool
let get_verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1779  -> lookup_opt "verify_module" (as_list as_string)
let get___temp_no_proj: Prims.unit -> Prims.string Prims.list =
  fun uu____1786  -> lookup_opt "__temp_no_proj" (as_list as_string)
let get_version: Prims.unit -> Prims.bool =
  fun uu____1791  -> lookup_opt "version" as_bool
let get_warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____1794  -> lookup_opt "warn_default_effects" as_bool
let get_z3cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____1799  -> lookup_opt "z3cliopt" (as_list as_string)
let get_z3refresh: Prims.unit -> Prims.bool =
  fun uu____1804  -> lookup_opt "z3refresh" as_bool
let get_z3rlimit: Prims.unit -> Prims.int =
  fun uu____1807  -> lookup_opt "z3rlimit" as_int
let get_z3rlimit_factor: Prims.unit -> Prims.int =
  fun uu____1810  -> lookup_opt "z3rlimit_factor" as_int
let get_z3seed: Prims.unit -> Prims.int =
  fun uu____1813  -> lookup_opt "z3seed" as_int
let get_no_positivity: Prims.unit -> Prims.bool =
  fun uu____1816  -> lookup_opt "__no_positivity" as_bool
let get_ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____1819  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool
let dlevel: Prims.string -> debug_level_t =
  fun uu___64_1822  ->
    match uu___64_1822 with
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
let rec specs_with_types:
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun uu____2829  ->
    let uu____2840 =
      let uu____2851 =
        let uu____2862 =
          let uu____2871 = let uu____2872 = mk_bool true in Const uu____2872 in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2871,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying") in
        let uu____2873 =
          let uu____2884 =
            let uu____2895 =
              let uu____2906 =
                let uu____2917 =
                  let uu____2928 =
                    let uu____2939 =
                      let uu____2948 =
                        let uu____2949 = mk_bool true in Const uu____2949 in
                      (FStar_Getopt.noshort, "detail_errors", uu____2948,
                        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1") in
                    let uu____2950 =
                      let uu____2961 =
                        let uu____2970 =
                          let uu____2971 = mk_bool true in Const uu____2971 in
                        (FStar_Getopt.noshort, "detail_hint_replay",
                          uu____2970,
                          "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1") in
                      let uu____2972 =
                        let uu____2983 =
                          let uu____2992 =
                            let uu____2993 = mk_bool true in Const uu____2993 in
                          (FStar_Getopt.noshort, "doc", uu____2992,
                            "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.") in
                        let uu____2994 =
                          let uu____3005 =
                            let uu____3016 =
                              let uu____3025 =
                                let uu____3026 = mk_bool true in
                                Const uu____3026 in
                              (FStar_Getopt.noshort, "eager_inference",
                                uu____3025,
                                "Solve all type-inference constraints eagerly; more efficient but at the cost of generality") in
                            let uu____3027 =
                              let uu____3038 =
                                let uu____3047 =
                                  let uu____3048 = mk_bool true in
                                  Const uu____3048 in
                                (FStar_Getopt.noshort, "explicit_deps",
                                  uu____3047,
                                  "Do not find dependencies automatically, the user provides them on the command-line") in
                              let uu____3049 =
                                let uu____3060 =
                                  let uu____3069 =
                                    let uu____3070 = mk_bool true in
                                    Const uu____3070 in
                                  (FStar_Getopt.noshort, "extract_all",
                                    uu____3069,
                                    "Discover the complete dependency graph and do not stop at interface boundaries") in
                                let uu____3071 =
                                  let uu____3082 =
                                    let uu____3093 =
                                      let uu____3104 =
                                        let uu____3115 =
                                          let uu____3126 =
                                            let uu____3135 =
                                              let uu____3136 = mk_bool true in
                                              Const uu____3136 in
                                            (FStar_Getopt.noshort,
                                              "hide_uvar_nums", uu____3135,
                                              "Don't print unification variable numbers") in
                                          let uu____3137 =
                                            let uu____3148 =
                                              let uu____3159 =
                                                let uu____3168 =
                                                  let uu____3169 =
                                                    mk_bool true in
                                                  Const uu____3169 in
                                                (FStar_Getopt.noshort,
                                                  "hint_info", uu____3168,
                                                  "Print information regarding hints (deprecated; use --query_stats instead)") in
                                              let uu____3170 =
                                                let uu____3181 =
                                                  let uu____3190 =
                                                    let uu____3191 =
                                                      mk_bool true in
                                                    Const uu____3191 in
                                                  (FStar_Getopt.noshort,
                                                    "in", uu____3190,
                                                    "Legacy interactive mode; reads input from stdin") in
                                                let uu____3192 =
                                                  let uu____3203 =
                                                    let uu____3212 =
                                                      let uu____3213 =
                                                        mk_bool true in
                                                      Const uu____3213 in
                                                    (FStar_Getopt.noshort,
                                                      "ide", uu____3212,
                                                      "JSON-based interactive mode for IDEs") in
                                                  let uu____3214 =
                                                    let uu____3225 =
                                                      let uu____3236 =
                                                        let uu____3245 =
                                                          let uu____3246 =
                                                            mk_bool true in
                                                          Const uu____3246 in
                                                        (FStar_Getopt.noshort,
                                                          "indent",
                                                          uu____3245,
                                                          "Parses and outputs the files on the command line") in
                                                      let uu____3247 =
                                                        let uu____3258 =
                                                          let uu____3269 =
                                                            let uu____3280 =
                                                              let uu____3289
                                                                =
                                                                let uu____3290
                                                                  =
                                                                  mk_bool
                                                                    true in
                                                                Const
                                                                  uu____3290 in
                                                              (FStar_Getopt.noshort,
                                                                "lax",
                                                                uu____3289,
                                                                "Run the lax-type checker only (admit all verification conditions)") in
                                                            let uu____3291 =
                                                              let uu____3302
                                                                =
                                                                let uu____3313
                                                                  =
                                                                  let uu____3322
                                                                    =
                                                                    let uu____3323
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3323 in
                                                                  (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3322,
                                                                    "Print types computed for data/val/let-bindings") in
                                                                let uu____3324
                                                                  =
                                                                  let uu____3335
                                                                    =
                                                                    let uu____3344
                                                                    =
                                                                    let uu____3345
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3345 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3344,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go") in
                                                                  let uu____3346
                                                                    =
                                                                    let uu____3357
                                                                    =
                                                                    let uu____3368
                                                                    =
                                                                    let uu____3379
                                                                    =
                                                                    let uu____3390
                                                                    =
                                                                    let uu____3399
                                                                    =
                                                                    let uu____3400
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3400 in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3399,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)") in
                                                                    let uu____3401
                                                                    =
                                                                    let uu____3412
                                                                    =
                                                                    let uu____3423
                                                                    =
                                                                    let uu____3432
                                                                    =
                                                                    let uu____3433
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3433 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3432,
                                                                    "Ignore the default module search paths") in
                                                                    let uu____3434
                                                                    =
                                                                    let uu____3445
                                                                    =
                                                                    let uu____3456
                                                                    =
                                                                    let uu____3465
                                                                    =
                                                                    let uu____3466
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3466 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3465,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)") in
                                                                    let uu____3467
                                                                    =
                                                                    let uu____3478
                                                                    =
                                                                    let uu____3489
                                                                    =
                                                                    let uu____3500
                                                                    =
                                                                    let uu____3509
                                                                    =
                                                                    let uu____3510
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3510 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3509,
                                                                    "Print the types of bound variables") in
                                                                    let uu____3511
                                                                    =
                                                                    let uu____3522
                                                                    =
                                                                    let uu____3531
                                                                    =
                                                                    let uu____3532
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3532 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3531,
                                                                    "Print inferred predicate transformers for all computation types") in
                                                                    let uu____3533
                                                                    =
                                                                    let uu____3544
                                                                    =
                                                                    let uu____3553
                                                                    =
                                                                    let uu____3554
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3554 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3553,
                                                                    "Print full names of variables") in
                                                                    let uu____3555
                                                                    =
                                                                    let uu____3566
                                                                    =
                                                                    let uu____3575
                                                                    =
                                                                    let uu____3576
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3576 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3575,
                                                                    "Print implicit arguments") in
                                                                    let uu____3577
                                                                    =
                                                                    let uu____3588
                                                                    =
                                                                    let uu____3597
                                                                    =
                                                                    let uu____3598
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3598 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3597,
                                                                    "Print universes") in
                                                                    let uu____3599
                                                                    =
                                                                    let uu____3610
                                                                    =
                                                                    let uu____3619
                                                                    =
                                                                    let uu____3620
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3620 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3619,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)") in
                                                                    let uu____3621
                                                                    =
                                                                    let uu____3632
                                                                    =
                                                                    let uu____3641
                                                                    =
                                                                    let uu____3642
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3642 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3641,
                                                                    "Print full names (deprecated; use --print_full_names instead)") in
                                                                    let uu____3643
                                                                    =
                                                                    let uu____3654
                                                                    =
                                                                    let uu____3663
                                                                    =
                                                                    let uu____3664
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3664 in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3663,
                                                                    "Print SMT query statistics") in
                                                                    let uu____3665
                                                                    =
                                                                    let uu____3676
                                                                    =
                                                                    let uu____3685
                                                                    =
                                                                    let uu____3686
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3686 in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3685,
                                                                    "Record a database of hints for efficient proof replay") in
                                                                    let uu____3687
                                                                    =
                                                                    let uu____3698
                                                                    =
                                                                    let uu____3709
                                                                    =
                                                                    let uu____3718
                                                                    =
                                                                    let uu____3719
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3719 in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3718,
                                                                    " ") in
                                                                    let uu____3720
                                                                    =
                                                                    let uu____3731
                                                                    =
                                                                    let uu____3742
                                                                    =
                                                                    let uu____3753
                                                                    =
                                                                    let uu____3764
                                                                    =
                                                                    let uu____3775
                                                                    =
                                                                    let uu____3786
                                                                    =
                                                                    let uu____3795
                                                                    =
                                                                    let uu____3796
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3796 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3795,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)") in
                                                                    let uu____3797
                                                                    =
                                                                    let uu____3808
                                                                    =
                                                                    let uu____3819
                                                                    =
                                                                    let uu____3828
                                                                    =
                                                                    let uu____3829
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3829 in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3828,
                                                                    "Print the time it takes to verify each top-level definition") in
                                                                    let uu____3830
                                                                    =
                                                                    let uu____3841
                                                                    =
                                                                    let uu____3850
                                                                    =
                                                                    let uu____3851
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3851 in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3850,
                                                                    "Don't print an error message; show an exception trace instead") in
                                                                    let uu____3852
                                                                    =
                                                                    let uu____3863
                                                                    =
                                                                    let uu____3872
                                                                    =
                                                                    let uu____3873
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3873 in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3872,
                                                                    "Emit output formatted for debugging") in
                                                                    let uu____3874
                                                                    =
                                                                    let uu____3885
                                                                    =
                                                                    let uu____3894
                                                                    =
                                                                    let uu____3895
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3895 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____3894,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)") in
                                                                    let uu____3896
                                                                    =
                                                                    let uu____3907
                                                                    =
                                                                    let uu____3916
                                                                    =
                                                                    let uu____3917
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3917 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____3916,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.") in
                                                                    let uu____3918
                                                                    =
                                                                    let uu____3929
                                                                    =
                                                                    let uu____3938
                                                                    =
                                                                    let uu____3939
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3939 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____3938,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)") in
                                                                    let uu____3940
                                                                    =
                                                                    let uu____3951
                                                                    =
                                                                    let uu____3960
                                                                    =
                                                                    let uu____3961
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3961 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____3960,
                                                                    "Use a previously recorded hints database for proof replay") in
                                                                    let uu____3962
                                                                    =
                                                                    let uu____3973
                                                                    =
                                                                    let uu____3982
                                                                    =
                                                                    let uu____3983
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3983 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____3982,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database") in
                                                                    let uu____3984
                                                                    =
                                                                    let uu____3995
                                                                    =
                                                                    let uu____4006
                                                                    =
                                                                    let uu____4015
                                                                    =
                                                                    let uu____4016
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4016 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4015,
                                                                    "Do not run the tactic engine before discharging a VC") in
                                                                    let uu____4017
                                                                    =
                                                                    let uu____4028
                                                                    =
                                                                    let uu____4039
                                                                    =
                                                                    let uu____4048
                                                                    =
                                                                    let uu____4049
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4049 in
                                                                    (FStar_Getopt.noshort,
                                                                    "verify_all",
                                                                    uu____4048,
                                                                    "With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.") in
                                                                    let uu____4050
                                                                    =
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
                                                                    let uu____4100
                                                                    =
                                                                    let uu____4101
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4101 in
                                                                    ((fun
                                                                    uu____4106
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____4100) in
                                                                    WithSideEffect
                                                                    uu____4093 in
                                                                    (118,
                                                                    "version",
                                                                    uu____4092,
                                                                    "Display version number") in
                                                                    let uu____4108
                                                                    =
                                                                    let uu____4119
                                                                    =
                                                                    let uu____4128
                                                                    =
                                                                    let uu____4129
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4129 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4128,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)") in
                                                                    let uu____4130
                                                                    =
                                                                    let uu____4141
                                                                    =
                                                                    let uu____4152
                                                                    =
                                                                    let uu____4161
                                                                    =
                                                                    let uu____4162
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4162 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4161,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness") in
                                                                    let uu____4163
                                                                    =
                                                                    let uu____4174
                                                                    =
                                                                    let uu____4185
                                                                    =
                                                                    let uu____4196
                                                                    =
                                                                    let uu____4207
                                                                    =
                                                                    let uu____4216
                                                                    =
                                                                    let uu____4217
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4217 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4216,
                                                                    "Don't check positivity of inductive types") in
                                                                    let uu____4218
                                                                    =
                                                                    let uu____4229
                                                                    =
                                                                    let uu____4238
                                                                    =
                                                                    let uu____4239
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4239 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4238,
                                                                    "Do not eta-expand coertions in generated OCaml") in
                                                                    let uu____4240
                                                                    =
                                                                    let uu____4251
                                                                    =
                                                                    let uu____4260
                                                                    =
                                                                    let uu____4261
                                                                    =
                                                                    let uu____4268
                                                                    =
                                                                    let uu____4269
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4269 in
                                                                    ((fun
                                                                    uu____4274
                                                                     ->
                                                                    (
                                                                    let uu____4276
                                                                    =
                                                                    specs () in
                                                                    display_usage_aux
                                                                    uu____4276);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____4268) in
                                                                    WithSideEffect
                                                                    uu____4261 in
                                                                    (104,
                                                                    "help",
                                                                    uu____4260,
                                                                    "Display this information") in
                                                                    [uu____4251] in
                                                                    uu____4229
                                                                    ::
                                                                    uu____4240 in
                                                                    uu____4207
                                                                    ::
                                                                    uu____4218 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4196 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4185 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4174 in
                                                                    uu____4152
                                                                    ::
                                                                    uu____4163 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4141 in
                                                                    uu____4119
                                                                    ::
                                                                    uu____4130 in
                                                                    uu____4083
                                                                    ::
                                                                    uu____4108 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4072 in
                                                                    (FStar_Getopt.noshort,
                                                                    "verify_module",
                                                                    (Accumulated
                                                                    (PostProcessed
                                                                    (pp_lowercase,
                                                                    (SimpleStr
                                                                    "module_name")))),
                                                                    "Name of the module to verify")
                                                                    ::
                                                                    uu____4061 in
                                                                    uu____4039
                                                                    ::
                                                                    uu____4050 in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4028 in
                                                                    uu____4006
                                                                    ::
                                                                    uu____4017 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____3995 in
                                                                    uu____3973
                                                                    ::
                                                                    uu____3984 in
                                                                    uu____3951
                                                                    ::
                                                                    uu____3962 in
                                                                    uu____3929
                                                                    ::
                                                                    uu____3940 in
                                                                    uu____3907
                                                                    ::
                                                                    uu____3918 in
                                                                    uu____3885
                                                                    ::
                                                                    uu____3896 in
                                                                    uu____3863
                                                                    ::
                                                                    uu____3874 in
                                                                    uu____3841
                                                                    ::
                                                                    uu____3852 in
                                                                    uu____3819
                                                                    ::
                                                                    uu____3830 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3808 in
                                                                    uu____3786
                                                                    ::
                                                                    uu____3797 in
                                                                    (FStar_Getopt.noshort,
                                                                    "split_cases",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Partition VC of a match into groups of <positive_integer> cases")
                                                                    ::
                                                                    uu____3775 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3764 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3753 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3742 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3731 in
                                                                    uu____3709
                                                                    ::
                                                                    uu____3720 in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3698 in
                                                                    uu____3676
                                                                    ::
                                                                    uu____3687 in
                                                                    uu____3654
                                                                    ::
                                                                    uu____3665 in
                                                                    uu____3632
                                                                    ::
                                                                    uu____3643 in
                                                                    uu____3610
                                                                    ::
                                                                    uu____3621 in
                                                                    uu____3588
                                                                    ::
                                                                    uu____3599 in
                                                                    uu____3566
                                                                    ::
                                                                    uu____3577 in
                                                                    uu____3544
                                                                    ::
                                                                    uu____3555 in
                                                                    uu____3522
                                                                    ::
                                                                    uu____3533 in
                                                                    uu____3500
                                                                    ::
                                                                    uu____3511 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3489 in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3478 in
                                                                    uu____3456
                                                                    ::
                                                                    uu____3467 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Do not extract code from this module")
                                                                    ::
                                                                    uu____3445 in
                                                                    uu____3423
                                                                    ::
                                                                    uu____3434 in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3412 in
                                                                    uu____3390
                                                                    ::
                                                                    uu____3401 in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3379 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3368 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3357 in
                                                                  uu____3335
                                                                    ::
                                                                    uu____3346 in
                                                                uu____3313 ::
                                                                  uu____3324 in
                                                              (FStar_Getopt.noshort,
                                                                "load",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "module")),
                                                                "Load compiled module")
                                                                :: uu____3302 in
                                                            uu____3280 ::
                                                              uu____3291 in
                                                          (FStar_Getopt.noshort,
                                                            "initial_ifuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                            :: uu____3269 in
                                                        (FStar_Getopt.noshort,
                                                          "initial_fuel",
                                                          (IntStr
                                                             "non-negative integer"),
                                                          "Number of unrolling of recursive functions to try initially (default 2)")
                                                          :: uu____3258 in
                                                      uu____3236 ::
                                                        uu____3247 in
                                                    (FStar_Getopt.noshort,
                                                      "include",
                                                      (ReverseAccumulated
                                                         (PathStr "path")),
                                                      "A directory in which to search for files included on the command line")
                                                      :: uu____3225 in
                                                  uu____3203 :: uu____3214 in
                                                uu____3181 :: uu____3192 in
                                              uu____3159 :: uu____3170 in
                                            (FStar_Getopt.noshort,
                                              "hint_file", (PathStr "path"),
                                              "Read/write hints to <path> (instead of module-specific hints files)")
                                              :: uu____3148 in
                                          uu____3126 :: uu____3137 in
                                        (FStar_Getopt.noshort,
                                          "gen_native_tactics",
                                          (PathStr "[path]"),
                                          "Compile all user tactics used in the module in <path>")
                                          :: uu____3115 in
                                      (FStar_Getopt.noshort, "fstar_home",
                                        (PathStr "dir"),
                                        "Set the FSTAR_HOME variable to <dir>")
                                        :: uu____3104 in
                                    (FStar_Getopt.noshort,
                                      "extract_namespace",
                                      (Accumulated
                                         (PostProcessed
                                            (pp_lowercase,
                                              (SimpleStr "namespace name")))),
                                      "Only extract modules in the specified namespace")
                                      :: uu____3093 in
                                  (FStar_Getopt.noshort, "extract_module",
                                    (Accumulated
                                       (PostProcessed
                                          (pp_lowercase,
                                            (SimpleStr "module_name")))),
                                    "Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                    :: uu____3082 in
                                uu____3060 :: uu____3071 in
                              uu____3038 :: uu____3049 in
                            uu____3016 :: uu____3027 in
                          (FStar_Getopt.noshort, "dump_module",
                            (Accumulated (SimpleStr "module_name")), "") ::
                            uu____3005 in
                        uu____2983 :: uu____2994 in
                      uu____2961 :: uu____2972 in
                    uu____2939 :: uu____2950 in
                  (FStar_Getopt.noshort, "dep", (EnumStr ["make"; "graph"]),
                    "Output the transitive closure of the dependency graph in a format suitable for the given tool")
                    :: uu____2928 in
                (FStar_Getopt.noshort, "debug_level",
                  (Accumulated
                     (OpenEnumStr
                        (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                  "Control the verbosity of debugging info") :: uu____2917 in
              (FStar_Getopt.noshort, "debug",
                (Accumulated (SimpleStr "module_name")),
                "Print lots of debugging information while checking module")
                :: uu____2906 in
            (FStar_Getopt.noshort, "codegen-lib",
              (Accumulated (SimpleStr "namespace")),
              "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
              :: uu____2895 in
          (FStar_Getopt.noshort, "codegen",
            (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "tactics"]),
            "Generate code for execution") :: uu____2884 in
        uu____2862 :: uu____2873 in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2851 in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2840
and specs: Prims.unit -> FStar_Getopt.opt Prims.list =
  fun uu____4979  ->
    let uu____4982 = specs_with_types () in
    FStar_List.map
      (fun uu____5007  ->
         match uu____5007 with
         | (short,long,typ,doc) ->
             let uu____5020 =
               let uu____5031 = arg_spec_of_opt_type long typ in
               (short, long, uu____5031, doc) in
             mk_spec uu____5020) uu____4982
let settable: Prims.string -> Prims.bool =
  fun uu___65_5038  ->
    match uu___65_5038 with
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
    | uu____5039 -> false
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
       (fun uu____5096  ->
          match uu____5096 with
          | (uu____5107,x,uu____5109,uu____5110) -> settable x))
let resettable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5156  ->
          match uu____5156 with
          | (uu____5167,x,uu____5169,uu____5170) -> resettable x))
let display_usage: Prims.unit -> Prims.unit =
  fun uu____5177  ->
    let uu____5178 = specs () in display_usage_aux uu____5178
let fstar_home: Prims.unit -> Prims.string =
  fun uu____5193  ->
    let uu____5194 = get_fstar_home () in
    match uu____5194 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        ((let uu____5200 =
            let uu____5205 = mk_string x1 in ("fstar_home", uu____5205) in
          set_option' uu____5200);
         x1)
    | FStar_Pervasives_Native.Some x -> x
exception File_argument of Prims.string
let uu___is_File_argument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____5213 -> true
    | uu____5214 -> false
let __proj__File_argument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____5221 -> uu____5221
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
          let uu____5265 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____5265
let file_list_: Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let parse_cmd_line:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____5287  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5292 =
             let uu____5295 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____5295 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____5292) in
    let uu____5398 =
      let uu____5401 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5401 in
    (res, uu____5398)
let file_list: Prims.unit -> Prims.string Prims.list =
  fun uu____5460  -> FStar_ST.op_Bang file_list_
let restore_cmd_line_options: Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____5520 = specs () in
       FStar_Getopt.parse_cmdline uu____5520 (fun x  -> ()) in
     (let uu____5526 =
        let uu____5531 =
          let uu____5532 = FStar_List.map mk_string old_verify_module in
          List uu____5532 in
        ("verify_module", uu____5531) in
      set_option' uu____5526);
     r)
let module_name_of_file_name: Prims.string -> Prims.string =
  fun f  ->
    let f1 = FStar_Util.basename f in
    let f2 =
      let uu____5540 =
        let uu____5541 =
          let uu____5542 =
            let uu____5543 = FStar_Util.get_file_extension f1 in
            FStar_String.length uu____5543 in
          (FStar_String.length f1) - uu____5542 in
        uu____5541 - (Prims.parse_int "1") in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5540 in
    FStar_String.lowercase f2
let should_verify: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5547 = get_lax () in
    if uu____5547
    then false
    else
      (let uu____5549 = get_verify_all () in
       if uu____5549
       then true
       else
         (let uu____5551 = get_verify_module () in
          match uu____5551 with
          | [] ->
              let uu____5554 = file_list () in
              FStar_List.existsML
                (fun f  ->
                   let uu____5560 = module_name_of_file_name f in
                   uu____5560 = m) uu____5554
          | l -> FStar_List.contains (FStar_String.lowercase m) l))
let should_verify_file: Prims.string -> Prims.bool =
  fun fn  ->
    let uu____5567 = module_name_of_file_name fn in should_verify uu____5567
let dont_gen_projectors: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5571 = get___temp_no_proj () in
    FStar_List.contains m uu____5571
let should_print_message: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5577 = should_verify m in
    if uu____5577 then m <> "Prims" else false
let include_path: Prims.unit -> Prims.string Prims.list =
  fun uu____5583  ->
    let uu____5584 = get_no_default_includes () in
    if uu____5584
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____5592 =
         let uu____5595 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____5595
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____5608 =
         let uu____5611 = get_include () in
         FStar_List.append uu____5611 ["."] in
       FStar_List.append uu____5592 uu____5608)
let find_file: Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____5619 = FStar_Util.is_path_absolute filename in
    if uu____5619
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5626 =
         let uu____5629 = include_path () in FStar_List.rev uu____5629 in
       FStar_Util.find_map uu____5626
         (fun p  ->
            let path = FStar_Util.join_paths p filename in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
let prims: Prims.unit -> Prims.string =
  fun uu____5641  ->
    let uu____5642 = get_prims () in
    match uu____5642 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst" in
        let uu____5646 = find_file filename in
        (match uu____5646 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5650 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename in
             failwith uu____5650)
    | FStar_Pervasives_Native.Some x -> x
let prims_basename: Prims.unit -> Prims.string =
  fun uu____5654  ->
    let uu____5655 = prims () in FStar_Util.basename uu____5655
let pervasives: Prims.unit -> Prims.string =
  fun uu____5658  ->
    let filename = "FStar.Pervasives.fst" in
    let uu____5660 = find_file filename in
    match uu____5660 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5664 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5664
let pervasives_basename: Prims.unit -> Prims.string =
  fun uu____5667  ->
    let uu____5668 = pervasives () in FStar_Util.basename uu____5668
let pervasives_native_basename: Prims.unit -> Prims.string =
  fun uu____5671  ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____5673 = find_file filename in
    match uu____5673 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5677 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5677
let prepend_output_dir: Prims.string -> Prims.string =
  fun fname  ->
    let uu____5681 = get_odir () in
    match uu____5681 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
let __temp_no_proj: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5688 = get___temp_no_proj () in
    FStar_All.pipe_right uu____5688 (FStar_List.contains s)
let admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____5695  -> get_admit_smt_queries ()
let admit_except: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5700  -> get_admit_except ()
let cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____5703  -> get_cache_checked_modules ()
let codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5708  -> get_codegen ()
let codegen_libs: Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____5715  ->
    let uu____5716 = get_codegen_lib () in
    FStar_All.pipe_right uu____5716
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
let debug_any: Prims.unit -> Prims.bool =
  fun uu____5731  -> let uu____5732 = get_debug () in uu____5732 <> []
let debug_at_level: Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      (let uu____5745 = get_debug () in
       FStar_All.pipe_right uu____5745 (FStar_List.contains modul)) &&
        (debug_level_geq level)
let dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5754  -> get_dep ()
let detail_errors: Prims.unit -> Prims.bool =
  fun uu____5757  -> get_detail_errors ()
let detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____5760  -> get_detail_hint_replay ()
let doc: Prims.unit -> Prims.bool = fun uu____5763  -> get_doc ()
let dump_module: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5767 = get_dump_module () in
    FStar_All.pipe_right uu____5767 (FStar_List.contains s)
let eager_inference: Prims.unit -> Prims.bool =
  fun uu____5774  -> get_eager_inference ()
let explicit_deps: Prims.unit -> Prims.bool =
  fun uu____5777  -> get_explicit_deps ()
let extract_all: Prims.unit -> Prims.bool =
  fun uu____5780  -> get_extract_all ()
let fs_typ_app: Prims.string -> Prims.bool =
  fun filename  ->
    let uu____5784 = FStar_ST.op_Bang light_off_files in
    FStar_List.contains filename uu____5784
let gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5841  -> get_gen_native_tactics ()
let full_context_dependency: Prims.unit -> Prims.bool =
  fun uu____5844  -> true
let hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____5847  -> get_hide_uvar_nums ()
let hint_info: Prims.unit -> Prims.bool =
  fun uu____5850  -> (get_hint_info ()) || (get_query_stats ())
let hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5855  -> get_hint_file ()
let ide: Prims.unit -> Prims.bool = fun uu____5858  -> get_ide ()
let indent: Prims.unit -> Prims.bool = fun uu____5861  -> get_indent ()
let initial_fuel: Prims.unit -> Prims.int =
  fun uu____5864  ->
    let uu____5865 = get_initial_fuel () in
    let uu____5866 = get_max_fuel () in Prims.min uu____5865 uu____5866
let initial_ifuel: Prims.unit -> Prims.int =
  fun uu____5869  ->
    let uu____5870 = get_initial_ifuel () in
    let uu____5871 = get_max_ifuel () in Prims.min uu____5870 uu____5871
let interactive: Prims.unit -> Prims.bool =
  fun uu____5874  -> (get_in ()) || (get_ide ())
let lax: Prims.unit -> Prims.bool = fun uu____5877  -> get_lax ()
let load: Prims.unit -> Prims.string Prims.list =
  fun uu____5882  -> get_load ()
let legacy_interactive: Prims.unit -> Prims.bool =
  fun uu____5885  -> get_in ()
let log_queries: Prims.unit -> Prims.bool =
  fun uu____5888  -> get_log_queries ()
let log_types: Prims.unit -> Prims.bool = fun uu____5891  -> get_log_types ()
let max_fuel: Prims.unit -> Prims.int = fun uu____5894  -> get_max_fuel ()
let max_ifuel: Prims.unit -> Prims.int = fun uu____5897  -> get_max_ifuel ()
let min_fuel: Prims.unit -> Prims.int = fun uu____5900  -> get_min_fuel ()
let ml_ish: Prims.unit -> Prims.bool = fun uu____5903  -> get_MLish ()
let set_ml_ish: Prims.unit -> Prims.unit =
  fun uu____5906  -> set_option "MLish" (Bool true)
let n_cores: Prims.unit -> Prims.int = fun uu____5909  -> get_n_cores ()
let no_default_includes: Prims.unit -> Prims.bool =
  fun uu____5912  -> get_no_default_includes ()
let no_extract: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5916 = get_no_extract () in
    FStar_All.pipe_right uu____5916 (FStar_List.contains s)
let no_location_info: Prims.unit -> Prims.bool =
  fun uu____5923  -> get_no_location_info ()
let output_dir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5928  -> get_odir ()
let ugly: Prims.unit -> Prims.bool = fun uu____5931  -> get_ugly ()
let print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____5934  -> get_print_bound_var_types ()
let print_effect_args: Prims.unit -> Prims.bool =
  fun uu____5937  -> get_print_effect_args ()
let print_implicits: Prims.unit -> Prims.bool =
  fun uu____5940  -> get_print_implicits ()
let print_real_names: Prims.unit -> Prims.bool =
  fun uu____5943  -> (get_prn ()) || (get_print_full_names ())
let print_universes: Prims.unit -> Prims.bool =
  fun uu____5946  -> get_print_universes ()
let print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____5949  -> (get_print_z3_statistics ()) || (get_query_stats ())
let query_stats: Prims.unit -> Prims.bool =
  fun uu____5952  -> get_query_stats ()
let record_hints: Prims.unit -> Prims.bool =
  fun uu____5955  -> get_record_hints ()
let reuse_hint_for: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____5960  -> get_reuse_hint_for ()
let silent: Prims.unit -> Prims.bool = fun uu____5963  -> get_silent ()
let smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____5966  -> get_smtencoding_elim_box ()
let smtencoding_nl_arith_native: Prims.unit -> Prims.bool =
  fun uu____5969  ->
    let uu____5970 = get_smtencoding_nl_arith_repr () in
    uu____5970 = "native"
let smtencoding_nl_arith_wrapped: Prims.unit -> Prims.bool =
  fun uu____5973  ->
    let uu____5974 = get_smtencoding_nl_arith_repr () in
    uu____5974 = "wrapped"
let smtencoding_nl_arith_default: Prims.unit -> Prims.bool =
  fun uu____5977  ->
    let uu____5978 = get_smtencoding_nl_arith_repr () in
    uu____5978 = "boxwrap"
let smtencoding_l_arith_native: Prims.unit -> Prims.bool =
  fun uu____5981  ->
    let uu____5982 = get_smtencoding_l_arith_repr () in uu____5982 = "native"
let smtencoding_l_arith_default: Prims.unit -> Prims.bool =
  fun uu____5985  ->
    let uu____5986 = get_smtencoding_l_arith_repr () in
    uu____5986 = "boxwrap"
let split_cases: Prims.unit -> Prims.int =
  fun uu____5989  -> get_split_cases ()
let tactic_trace: Prims.unit -> Prims.bool =
  fun uu____5992  -> get_tactic_trace ()
let tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____5995  -> get_tactic_trace_d ()
let timing: Prims.unit -> Prims.bool = fun uu____5998  -> get_timing ()
let trace_error: Prims.unit -> Prims.bool =
  fun uu____6001  -> get_trace_error ()
let unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____6004  -> get_unthrottle_inductives ()
let unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____6007  -> get_unsafe_tactic_exec ()
let use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____6010  -> get_use_eq_at_higher_order ()
let use_hints: Prims.unit -> Prims.bool = fun uu____6013  -> get_use_hints ()
let use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____6016  -> get_use_hint_hashes ()
let use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____6021  -> get_use_native_tactics ()
let use_tactics: Prims.unit -> Prims.bool =
  fun uu____6024  -> get_use_tactics ()
let using_facts_from:
  Prims.unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____6033  ->
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if FStar_Util.starts_with s "-"
        then
          (let path =
             let uu____6062 =
               FStar_Util.substring_from s (Prims.parse_int "1") in
             FStar_Ident.path_of_text uu____6062 in
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
    let uu____6098 = get_using_facts_from () in
    match uu____6098 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns ->
        let uu____6130 = FStar_List.collect parse_setting ns in
        FStar_All.pipe_right uu____6130 FStar_List.rev
let verify_all: Prims.unit -> Prims.bool =
  fun uu____6169  -> get_verify_all ()
let verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____6174  -> get_verify_module ()
let warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____6177  -> get_warn_default_effects ()
let z3_exe: Prims.unit -> Prims.string =
  fun uu____6180  ->
    let uu____6181 = get_smt () in
    match uu____6181 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let z3_cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____6189  -> get_z3cliopt ()
let z3_refresh: Prims.unit -> Prims.bool =
  fun uu____6192  -> get_z3refresh ()
let z3_rlimit: Prims.unit -> Prims.int = fun uu____6195  -> get_z3rlimit ()
let z3_rlimit_factor: Prims.unit -> Prims.int =
  fun uu____6198  -> get_z3rlimit_factor ()
let z3_seed: Prims.unit -> Prims.int = fun uu____6201  -> get_z3seed ()
let no_positivity: Prims.unit -> Prims.bool =
  fun uu____6204  -> get_no_positivity ()
let ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____6207  -> get_ml_no_eta_expand_coertions ()
let should_extract: Prims.string -> Prims.bool =
  fun m  ->
    (let uu____6213 = no_extract m in Prims.op_Negation uu____6213) &&
      ((extract_all ()) ||
         (let uu____6216 = get_extract_module () in
          match uu____6216 with
          | [] ->
              let uu____6219 = get_extract_namespace () in
              (match uu____6219 with
               | [] -> true
               | ns ->
                   FStar_Util.for_some
                     (FStar_Util.starts_with (FStar_String.lowercase m)) ns)
          | l -> FStar_List.contains (FStar_String.lowercase m) l))
let codegen_fsharp: Prims.unit -> Prims.bool =
  fun uu____6230  ->
    let uu____6231 = codegen () in
    uu____6231 = (FStar_Pervasives_Native.Some "FSharp")