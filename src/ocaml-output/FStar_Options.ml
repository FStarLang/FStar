open Prims
type debug_level_t =
  | Low
  | Medium
  | High
  | Extreme
  | Other of Prims.string[@@deriving show]
let uu___is_Low: debug_level_t -> Prims.bool =
  fun projectee  -> match projectee with | Low  -> true | uu____9 -> false
let uu___is_Medium: debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____14 -> false
let uu___is_High: debug_level_t -> Prims.bool =
  fun projectee  -> match projectee with | High  -> true | uu____19 -> false
let uu___is_Extreme: debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____24 -> false
let uu___is_Other: debug_level_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____30 -> false
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
    match projectee with | Bool _0 -> true | uu____66 -> false
let __proj__Bool__item___0: option_val -> Prims.bool =
  fun projectee  -> match projectee with | Bool _0 -> _0
let uu___is_String: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____80 -> false
let __proj__String__item___0: option_val -> Prims.string =
  fun projectee  -> match projectee with | String _0 -> _0
let uu___is_Path: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____94 -> false
let __proj__Path__item___0: option_val -> Prims.string =
  fun projectee  -> match projectee with | Path _0 -> _0
let uu___is_Int: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____108 -> false
let __proj__Int__item___0: option_val -> Prims.int =
  fun projectee  -> match projectee with | Int _0 -> _0
let uu___is_List: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____124 -> false
let __proj__List__item___0: option_val -> option_val Prims.list =
  fun projectee  -> match projectee with | List _0 -> _0
let uu___is_Unset: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____143 -> false
let mk_bool: Prims.bool -> option_val = fun _0_28  -> Bool _0_28
let mk_string: Prims.string -> option_val = fun _0_29  -> String _0_29
let mk_path: Prims.string -> option_val = fun _0_30  -> Path _0_30
let mk_int: Prims.int -> option_val = fun _0_31  -> Int _0_31
let mk_list: option_val Prims.list -> option_val = fun _0_32  -> List _0_32
type options =
  | Set
  | Reset
  | Restore[@@deriving show]
let uu___is_Set: options -> Prims.bool =
  fun projectee  -> match projectee with | Set  -> true | uu____165 -> false
let uu___is_Reset: options -> Prims.bool =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____170 -> false
let uu___is_Restore: options -> Prims.bool =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____175 -> false
let __unit_tests__: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let __unit_tests: Prims.unit -> Prims.bool =
  fun uu____188  -> FStar_ST.op_Bang __unit_tests__
let __set_unit_tests: Prims.unit -> Prims.unit =
  fun uu____238  -> FStar_ST.op_Colon_Equals __unit_tests__ true
let __clear_unit_tests: Prims.unit -> Prims.unit =
  fun uu____288  -> FStar_ST.op_Colon_Equals __unit_tests__ false
let as_bool: option_val -> Prims.bool =
  fun uu___59_338  ->
    match uu___59_338 with
    | Bool b -> b
    | uu____340 -> failwith "Impos: expected Bool"
let as_int: option_val -> Prims.int =
  fun uu___60_344  ->
    match uu___60_344 with
    | Int b -> b
    | uu____346 -> failwith "Impos: expected Int"
let as_string: option_val -> Prims.string =
  fun uu___61_350  ->
    match uu___61_350 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____353 -> failwith "Impos: expected String"
let as_list': option_val -> option_val Prims.list =
  fun uu___62_359  ->
    match uu___62_359 with
    | List ts -> ts
    | uu____365 -> failwith "Impos: expected List"
let as_list:
  'Auu____374 .
    (option_val -> 'Auu____374) -> option_val -> 'Auu____374 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____390 = as_list' x in
      FStar_All.pipe_right uu____390 (FStar_List.map as_t)
let as_option:
  'Auu____403 .
    (option_val -> 'Auu____403) ->
      option_val -> 'Auu____403 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___63_416  ->
      match uu___63_416 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____420 = as_t v1 in FStar_Pervasives_Native.Some uu____420
type optionstate = option_val FStar_Util.smap[@@deriving show]
let fstar_options: optionstate Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let peek: Prims.unit -> optionstate =
  fun uu____439  ->
    let uu____440 = FStar_ST.op_Bang fstar_options in FStar_List.hd uu____440
let pop: Prims.unit -> Prims.unit =
  fun uu____496  ->
    let uu____497 = FStar_ST.op_Bang fstar_options in
    match uu____497 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____550::[] -> failwith "TOO MANY POPS!"
    | uu____551::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
let push: Prims.unit -> Prims.unit =
  fun uu____608  ->
    let uu____609 =
      let uu____612 =
        let uu____615 = peek () in FStar_Util.smap_copy uu____615 in
      let uu____618 = FStar_ST.op_Bang fstar_options in uu____612 ::
        uu____618 in
    FStar_ST.op_Colon_Equals fstar_options uu____609
let set: optionstate -> Prims.unit =
  fun o  ->
    let uu____729 = FStar_ST.op_Bang fstar_options in
    match uu____729 with
    | [] -> failwith "set on empty option stack"
    | uu____782::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
let set_option: Prims.string -> option_val -> Prims.unit =
  fun k  ->
    fun v1  -> let uu____844 = peek () in FStar_Util.smap_add uu____844 k v1
let set_option':
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> Prims.unit =
  fun uu____854  -> match uu____854 with | (k,v1) -> set_option k v1
let with_saved_options: 'a . (Prims.unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f () in pop (); retv)
let light_off_files: Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let add_light_off_file: Prims.string -> Prims.unit =
  fun filename  ->
    let uu____895 =
      let uu____898 = FStar_ST.op_Bang light_off_files in filename ::
        uu____898 in
    FStar_ST.op_Colon_Equals light_off_files uu____895
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
  fun uu____1362  ->
    let o = peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let clear: Prims.unit -> Prims.unit =
  fun uu____1378  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50") in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
let _run: Prims.unit = clear ()
let get_option: Prims.string -> option_val =
  fun s  ->
    let uu____1492 =
      let uu____1495 = peek () in FStar_Util.smap_try_find uu____1495 s in
    match uu____1492 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
let lookup_opt:
  'Auu____1505 . Prims.string -> (option_val -> 'Auu____1505) -> 'Auu____1505
  = fun s  -> fun c  -> c (get_option s)
let get_admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____1522  -> lookup_opt "admit_smt_queries" as_bool
let get_admit_except:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1528  -> lookup_opt "admit_except" (as_option as_string)
let get_cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____1534  -> lookup_opt "cache_checked_modules" as_bool
let get_codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1540  -> lookup_opt "codegen" (as_option as_string)
let get_codegen_lib: Prims.unit -> Prims.string Prims.list =
  fun uu____1548  -> lookup_opt "codegen-lib" (as_list as_string)
let get_debug: Prims.unit -> Prims.string Prims.list =
  fun uu____1556  -> lookup_opt "debug" (as_list as_string)
let get_debug_level: Prims.unit -> Prims.string Prims.list =
  fun uu____1564  -> lookup_opt "debug_level" (as_list as_string)
let get_dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1572  -> lookup_opt "dep" (as_option as_string)
let get_detail_errors: Prims.unit -> Prims.bool =
  fun uu____1578  -> lookup_opt "detail_errors" as_bool
let get_detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____1582  -> lookup_opt "detail_hint_replay" as_bool
let get_doc: Prims.unit -> Prims.bool =
  fun uu____1586  -> lookup_opt "doc" as_bool
let get_dump_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1592  -> lookup_opt "dump_module" (as_list as_string)
let get_eager_inference: Prims.unit -> Prims.bool =
  fun uu____1598  -> lookup_opt "eager_inference" as_bool
let get_explicit_deps: Prims.unit -> Prims.bool =
  fun uu____1602  -> lookup_opt "explicit_deps" as_bool
let get_extract_all: Prims.unit -> Prims.bool =
  fun uu____1606  -> lookup_opt "extract_all" as_bool
let get_extract_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1612  -> lookup_opt "extract_module" (as_list as_string)
let get_extract_namespace: Prims.unit -> Prims.string Prims.list =
  fun uu____1620  -> lookup_opt "extract_namespace" (as_list as_string)
let get_fs_typ_app: Prims.unit -> Prims.bool =
  fun uu____1626  -> lookup_opt "fs_typ_app" as_bool
let get_fstar_home: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1632  -> lookup_opt "fstar_home" (as_option as_string)
let get_gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1640  -> lookup_opt "gen_native_tactics" (as_option as_string)
let get_hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____1646  -> lookup_opt "hide_uvar_nums" as_bool
let get_hint_info: Prims.unit -> Prims.bool =
  fun uu____1650  -> lookup_opt "hint_info" as_bool
let get_hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1656  -> lookup_opt "hint_file" (as_option as_string)
let get_in: Prims.unit -> Prims.bool =
  fun uu____1662  -> lookup_opt "in" as_bool
let get_ide: Prims.unit -> Prims.bool =
  fun uu____1666  -> lookup_opt "ide" as_bool
let get_include: Prims.unit -> Prims.string Prims.list =
  fun uu____1672  -> lookup_opt "include" (as_list as_string)
let get_indent: Prims.unit -> Prims.bool =
  fun uu____1678  -> lookup_opt "indent" as_bool
let get_initial_fuel: Prims.unit -> Prims.int =
  fun uu____1682  -> lookup_opt "initial_fuel" as_int
let get_initial_ifuel: Prims.unit -> Prims.int =
  fun uu____1686  -> lookup_opt "initial_ifuel" as_int
let get_lax: Prims.unit -> Prims.bool =
  fun uu____1690  -> lookup_opt "lax" as_bool
let get_load: Prims.unit -> Prims.string Prims.list =
  fun uu____1696  -> lookup_opt "load" (as_list as_string)
let get_log_queries: Prims.unit -> Prims.bool =
  fun uu____1702  -> lookup_opt "log_queries" as_bool
let get_log_types: Prims.unit -> Prims.bool =
  fun uu____1706  -> lookup_opt "log_types" as_bool
let get_max_fuel: Prims.unit -> Prims.int =
  fun uu____1710  -> lookup_opt "max_fuel" as_int
let get_max_ifuel: Prims.unit -> Prims.int =
  fun uu____1714  -> lookup_opt "max_ifuel" as_int
let get_min_fuel: Prims.unit -> Prims.int =
  fun uu____1718  -> lookup_opt "min_fuel" as_int
let get_MLish: Prims.unit -> Prims.bool =
  fun uu____1722  -> lookup_opt "MLish" as_bool
let get_n_cores: Prims.unit -> Prims.int =
  fun uu____1726  -> lookup_opt "n_cores" as_int
let get_no_default_includes: Prims.unit -> Prims.bool =
  fun uu____1730  -> lookup_opt "no_default_includes" as_bool
let get_no_extract: Prims.unit -> Prims.string Prims.list =
  fun uu____1736  -> lookup_opt "no_extract" (as_list as_string)
let get_no_location_info: Prims.unit -> Prims.bool =
  fun uu____1742  -> lookup_opt "no_location_info" as_bool
let get_odir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1748  -> lookup_opt "odir" (as_option as_string)
let get_ugly: Prims.unit -> Prims.bool =
  fun uu____1754  -> lookup_opt "ugly" as_bool
let get_prims: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1760  -> lookup_opt "prims" (as_option as_string)
let get_print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____1766  -> lookup_opt "print_bound_var_types" as_bool
let get_print_effect_args: Prims.unit -> Prims.bool =
  fun uu____1770  -> lookup_opt "print_effect_args" as_bool
let get_print_full_names: Prims.unit -> Prims.bool =
  fun uu____1774  -> lookup_opt "print_full_names" as_bool
let get_print_implicits: Prims.unit -> Prims.bool =
  fun uu____1778  -> lookup_opt "print_implicits" as_bool
let get_print_universes: Prims.unit -> Prims.bool =
  fun uu____1782  -> lookup_opt "print_universes" as_bool
let get_print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____1786  -> lookup_opt "print_z3_statistics" as_bool
let get_prn: Prims.unit -> Prims.bool =
  fun uu____1790  -> lookup_opt "prn" as_bool
let get_query_stats: Prims.unit -> Prims.bool =
  fun uu____1794  -> lookup_opt "query_stats" as_bool
let get_record_hints: Prims.unit -> Prims.bool =
  fun uu____1798  -> lookup_opt "record_hints" as_bool
let get_reuse_hint_for:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1804  -> lookup_opt "reuse_hint_for" (as_option as_string)
let get_silent: Prims.unit -> Prims.bool =
  fun uu____1810  -> lookup_opt "silent" as_bool
let get_smt: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1816  -> lookup_opt "smt" (as_option as_string)
let get_smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____1822  -> lookup_opt "smtencoding.elim_box" as_bool
let get_smtencoding_nl_arith_repr: Prims.unit -> Prims.string =
  fun uu____1826  -> lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr: Prims.unit -> Prims.string =
  fun uu____1830  -> lookup_opt "smtencoding.l_arith_repr" as_string
let get_split_cases: Prims.unit -> Prims.int =
  fun uu____1834  -> lookup_opt "split_cases" as_int
let get_tactic_trace: Prims.unit -> Prims.bool =
  fun uu____1838  -> lookup_opt "tactic_trace" as_bool
let get_tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____1842  -> lookup_opt "tactic_trace_d" as_int
let get_timing: Prims.unit -> Prims.bool =
  fun uu____1846  -> lookup_opt "timing" as_bool
let get_trace_error: Prims.unit -> Prims.bool =
  fun uu____1850  -> lookup_opt "trace_error" as_bool
let get_unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____1854  -> lookup_opt "unthrottle_inductives" as_bool
let get_unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____1858  -> lookup_opt "unsafe_tactic_exec" as_bool
let get_use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____1862  -> lookup_opt "use_eq_at_higher_order" as_bool
let get_use_hints: Prims.unit -> Prims.bool =
  fun uu____1866  -> lookup_opt "use_hints" as_bool
let get_use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____1870  -> lookup_opt "use_hint_hashes" as_bool
let get_use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1876  -> lookup_opt "use_native_tactics" (as_option as_string)
let get_use_tactics: Prims.unit -> Prims.bool =
  fun uu____1882  ->
    let uu____1883 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____1883
let get_using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1891  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let get_verify_all: Prims.unit -> Prims.bool =
  fun uu____1901  -> lookup_opt "verify_all" as_bool
let get_verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1907  -> lookup_opt "verify_module" (as_list as_string)
let get___temp_no_proj: Prims.unit -> Prims.string Prims.list =
  fun uu____1915  -> lookup_opt "__temp_no_proj" (as_list as_string)
let get_version: Prims.unit -> Prims.bool =
  fun uu____1921  -> lookup_opt "version" as_bool
let get_warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____1925  -> lookup_opt "warn_default_effects" as_bool
let get_z3cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____1931  -> lookup_opt "z3cliopt" (as_list as_string)
let get_z3refresh: Prims.unit -> Prims.bool =
  fun uu____1937  -> lookup_opt "z3refresh" as_bool
let get_z3rlimit: Prims.unit -> Prims.int =
  fun uu____1941  -> lookup_opt "z3rlimit" as_int
let get_z3rlimit_factor: Prims.unit -> Prims.int =
  fun uu____1945  -> lookup_opt "z3rlimit_factor" as_int
let get_z3seed: Prims.unit -> Prims.int =
  fun uu____1949  -> lookup_opt "z3seed" as_int
let get_no_positivity: Prims.unit -> Prims.bool =
  fun uu____1953  -> lookup_opt "__no_positivity" as_bool
let get_ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____1957  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool
let dlevel: Prims.string -> debug_level_t =
  fun uu___64_1961  ->
    match uu___64_1961 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let one_debug_level_geq: debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1971 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let debug_level_geq: debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____1976 = get_debug_level () in
    FStar_All.pipe_right uu____1976
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
let universe_include_path_base_dirs: Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"]
let _version: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _platform: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _compiler: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _date: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _commit: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let display_version: Prims.unit -> Prims.unit =
  fun uu____2068  ->
    let uu____2069 =
      let uu____2070 = FStar_ST.op_Bang _version in
      let uu____2117 = FStar_ST.op_Bang _platform in
      let uu____2164 = FStar_ST.op_Bang _compiler in
      let uu____2211 = FStar_ST.op_Bang _date in
      let uu____2258 = FStar_ST.op_Bang _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2070
        uu____2117 uu____2164 uu____2211 uu____2258 in
    FStar_Util.print_string uu____2069
let display_usage_aux:
  'Auu____2311 'Auu____2312 .
    ('Auu____2312,Prims.string,'Auu____2311 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2359  ->
         match uu____2359 with
         | (uu____2370,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2381 =
                      let uu____2382 = FStar_Util.colorize_bold flag in
                      FStar_Util.format1 "  --%s\n" uu____2382 in
                    FStar_Util.print_string uu____2381
                  else
                    (let uu____2384 =
                       let uu____2385 = FStar_Util.colorize_bold flag in
                       FStar_Util.format2 "  --%s  %s\n" uu____2385 doc in
                     FStar_Util.print_string uu____2384)
              | FStar_Getopt.OneArg (uu____2386,argname) ->
                  if doc = ""
                  then
                    let uu____2392 =
                      let uu____2393 = FStar_Util.colorize_bold flag in
                      let uu____2394 = FStar_Util.colorize_bold argname in
                      FStar_Util.format2 "  --%s %s\n" uu____2393 uu____2394 in
                    FStar_Util.print_string uu____2392
                  else
                    (let uu____2396 =
                       let uu____2397 = FStar_Util.colorize_bold flag in
                       let uu____2398 = FStar_Util.colorize_bold argname in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2397
                         uu____2398 doc in
                     FStar_Util.print_string uu____2396))) specs
let mk_spec:
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____2423 = o in
    match uu____2423 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2453 =
                let uu____2454 = f () in set_option name uu____2454 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2465 = f x in set_option name uu____2465 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2481 = lookup_opt name (as_option as_list') in
        FStar_Util.dflt [] uu____2481 in
      mk_list (value :: prev_values)
let reverse_accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let uu____2502 =
        let uu____2505 = lookup_opt name as_list' in
        FStar_List.append uu____2505 [value] in
      mk_list uu____2502
let accumulate_string:
  'Auu____2518 .
    Prims.string ->
      ('Auu____2518 -> Prims.string) -> 'Auu____2518 -> Prims.unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2536 =
          let uu____2537 =
            let uu____2538 = post_processor value in mk_string uu____2538 in
          accumulated_option name uu____2537 in
        set_option name uu____2536
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
    match projectee with | Const _0 -> true | uu____2620 -> false
let __proj__Const__item___0: opt_type -> option_val =
  fun projectee  -> match projectee with | Const _0 -> _0
let uu___is_IntStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2634 -> false
let __proj__IntStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | IntStr _0 -> _0
let uu___is_BoolStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2647 -> false
let uu___is_PathStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2653 -> false
let __proj__PathStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | PathStr _0 -> _0
let uu___is_SimpleStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2667 -> false
let __proj__SimpleStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0
let uu___is_EnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2683 -> false
let __proj__EnumStr__item___0: opt_type -> Prims.string Prims.list =
  fun projectee  -> match projectee with | EnumStr _0 -> _0
let uu___is_OpenEnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2709 -> false
let __proj__OpenEnumStr__item___0:
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0
let uu___is_PostProcessed: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2747 -> false
let __proj__PostProcessed__item___0:
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0
let uu___is_Accumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2779 -> false
let __proj__Accumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | Accumulated _0 -> _0
let uu___is_ReverseAccumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2793 -> false
let __proj__ReverseAccumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0
let uu___is_WithSideEffect: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2813 -> false
let __proj__WithSideEffect__item___0:
  opt_type ->
    (Prims.unit -> Prims.unit,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | WithSideEffect _0 -> _0
exception InvalidArgument of Prims.string
let uu___is_InvalidArgument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2847 -> true
    | uu____2848 -> false
let __proj__InvalidArgument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2856 -> uu____2856
let rec parse_opt_val: Prims.string -> opt_type -> Prims.string -> option_val
  =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2873 ->
              let uu____2874 = FStar_Util.safe_int_of_string str_val in
              (match uu____2874 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2878 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name) in
              mk_bool uu____2878
          | PathStr uu____2881 -> mk_path str_val
          | SimpleStr uu____2882 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2887 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2900 = parse_opt_val opt_name elem_spec str_val in
              pp uu____2900
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
            let uu____2917 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1 in
            failwith uu____2917
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
    | PostProcessed (uu____2951,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2959,elem_spec) -> desc_of_opt_type elem_spec
let rec arg_spec_of_opt_type:
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ in
      let uu____2980 = desc_of_opt_type typ in
      match uu____2980 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2986  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
let pp_validate_dir: option_val -> option_val =
  fun p  -> let pp = as_string p in FStar_Util.mkdir false pp; p
let pp_lowercase: option_val -> option_val =
  fun s  ->
    let uu____3000 =
      let uu____3001 = as_string s in FStar_String.lowercase uu____3001 in
    mk_string uu____3000
let rec specs_with_types:
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun uu____3018  ->
    let uu____3029 =
      let uu____3040 =
        let uu____3051 =
          let uu____3060 = let uu____3061 = mk_bool true in Const uu____3061 in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____3060,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying") in
        let uu____3062 =
          let uu____3073 =
            let uu____3084 =
              let uu____3095 =
                let uu____3106 =
                  let uu____3117 =
                    let uu____3128 =
                      let uu____3137 =
                        let uu____3138 = mk_bool true in Const uu____3138 in
                      (FStar_Getopt.noshort, "detail_errors", uu____3137,
                        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1") in
                    let uu____3139 =
                      let uu____3150 =
                        let uu____3159 =
                          let uu____3160 = mk_bool true in Const uu____3160 in
                        (FStar_Getopt.noshort, "detail_hint_replay",
                          uu____3159,
                          "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1") in
                      let uu____3161 =
                        let uu____3172 =
                          let uu____3181 =
                            let uu____3182 = mk_bool true in Const uu____3182 in
                          (FStar_Getopt.noshort, "doc", uu____3181,
                            "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.") in
                        let uu____3183 =
                          let uu____3194 =
                            let uu____3205 =
                              let uu____3214 =
                                let uu____3215 = mk_bool true in
                                Const uu____3215 in
                              (FStar_Getopt.noshort, "eager_inference",
                                uu____3214,
                                "Solve all type-inference constraints eagerly; more efficient but at the cost of generality") in
                            let uu____3216 =
                              let uu____3227 =
                                let uu____3236 =
                                  let uu____3237 = mk_bool true in
                                  Const uu____3237 in
                                (FStar_Getopt.noshort, "explicit_deps",
                                  uu____3236,
                                  "Do not find dependencies automatically, the user provides them on the command-line") in
                              let uu____3238 =
                                let uu____3249 =
                                  let uu____3258 =
                                    let uu____3259 = mk_bool true in
                                    Const uu____3259 in
                                  (FStar_Getopt.noshort, "extract_all",
                                    uu____3258,
                                    "Discover the complete dependency graph and do not stop at interface boundaries") in
                                let uu____3260 =
                                  let uu____3271 =
                                    let uu____3282 =
                                      let uu____3293 =
                                        let uu____3304 =
                                          let uu____3315 =
                                            let uu____3324 =
                                              let uu____3325 = mk_bool true in
                                              Const uu____3325 in
                                            (FStar_Getopt.noshort,
                                              "hide_uvar_nums", uu____3324,
                                              "Don't print unification variable numbers") in
                                          let uu____3326 =
                                            let uu____3337 =
                                              let uu____3348 =
                                                let uu____3357 =
                                                  let uu____3358 =
                                                    mk_bool true in
                                                  Const uu____3358 in
                                                (FStar_Getopt.noshort,
                                                  "hint_info", uu____3357,
                                                  "Print information regarding hints (deprecated; use --query_stats instead)") in
                                              let uu____3359 =
                                                let uu____3370 =
                                                  let uu____3379 =
                                                    let uu____3380 =
                                                      mk_bool true in
                                                    Const uu____3380 in
                                                  (FStar_Getopt.noshort,
                                                    "in", uu____3379,
                                                    "Legacy interactive mode; reads input from stdin") in
                                                let uu____3381 =
                                                  let uu____3392 =
                                                    let uu____3401 =
                                                      let uu____3402 =
                                                        mk_bool true in
                                                      Const uu____3402 in
                                                    (FStar_Getopt.noshort,
                                                      "ide", uu____3401,
                                                      "JSON-based interactive mode for IDEs") in
                                                  let uu____3403 =
                                                    let uu____3414 =
                                                      let uu____3425 =
                                                        let uu____3434 =
                                                          let uu____3435 =
                                                            mk_bool true in
                                                          Const uu____3435 in
                                                        (FStar_Getopt.noshort,
                                                          "indent",
                                                          uu____3434,
                                                          "Parses and outputs the files on the command line") in
                                                      let uu____3436 =
                                                        let uu____3447 =
                                                          let uu____3458 =
                                                            let uu____3469 =
                                                              let uu____3478
                                                                =
                                                                let uu____3479
                                                                  =
                                                                  mk_bool
                                                                    true in
                                                                Const
                                                                  uu____3479 in
                                                              (FStar_Getopt.noshort,
                                                                "lax",
                                                                uu____3478,
                                                                "Run the lax-type checker only (admit all verification conditions)") in
                                                            let uu____3480 =
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
                                                                    "log_types",
                                                                    uu____3511,
                                                                    "Print types computed for data/val/let-bindings") in
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
                                                                    "log_queries",
                                                                    uu____3533,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go") in
                                                                  let uu____3535
                                                                    =
                                                                    let uu____3546
                                                                    =
                                                                    let uu____3557
                                                                    =
                                                                    let uu____3568
                                                                    =
                                                                    let uu____3579
                                                                    =
                                                                    let uu____3588
                                                                    =
                                                                    let uu____3589
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3589 in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3588,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)") in
                                                                    let uu____3590
                                                                    =
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
                                                                    "no_default_includes",
                                                                    uu____3621,
                                                                    "Ignore the default module search paths") in
                                                                    let uu____3623
                                                                    =
                                                                    let uu____3634
                                                                    =
                                                                    let uu____3645
                                                                    =
                                                                    let uu____3654
                                                                    =
                                                                    let uu____3655
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3655 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3654,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)") in
                                                                    let uu____3656
                                                                    =
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
                                                                    "print_bound_var_types",
                                                                    uu____3698,
                                                                    "Print the types of bound variables") in
                                                                    let uu____3700
                                                                    =
                                                                    let uu____3711
                                                                    =
                                                                    let uu____3720
                                                                    =
                                                                    let uu____3721
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3721 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3720,
                                                                    "Print inferred predicate transformers for all computation types") in
                                                                    let uu____3722
                                                                    =
                                                                    let uu____3733
                                                                    =
                                                                    let uu____3742
                                                                    =
                                                                    let uu____3743
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3743 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3742,
                                                                    "Print full names of variables") in
                                                                    let uu____3744
                                                                    =
                                                                    let uu____3755
                                                                    =
                                                                    let uu____3764
                                                                    =
                                                                    let uu____3765
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3765 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3764,
                                                                    "Print implicit arguments") in
                                                                    let uu____3766
                                                                    =
                                                                    let uu____3777
                                                                    =
                                                                    let uu____3786
                                                                    =
                                                                    let uu____3787
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3787 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3786,
                                                                    "Print universes") in
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
                                                                    "print_z3_statistics",
                                                                    uu____3808,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)") in
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
                                                                    "prn",
                                                                    uu____3830,
                                                                    "Print full names (deprecated; use --print_full_names instead)") in
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
                                                                    "query_stats",
                                                                    uu____3852,
                                                                    "Print SMT query statistics") in
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
                                                                    "record_hints",
                                                                    uu____3874,
                                                                    "Record a database of hints for efficient proof replay") in
                                                                    let uu____3876
                                                                    =
                                                                    let uu____3887
                                                                    =
                                                                    let uu____3898
                                                                    =
                                                                    let uu____3907
                                                                    =
                                                                    let uu____3908
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3908 in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3907,
                                                                    " ") in
                                                                    let uu____3909
                                                                    =
                                                                    let uu____3920
                                                                    =
                                                                    let uu____3931
                                                                    =
                                                                    let uu____3942
                                                                    =
                                                                    let uu____3953
                                                                    =
                                                                    let uu____3964
                                                                    =
                                                                    let uu____3975
                                                                    =
                                                                    let uu____3984
                                                                    =
                                                                    let uu____3985
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3985 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3984,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)") in
                                                                    let uu____3986
                                                                    =
                                                                    let uu____3997
                                                                    =
                                                                    let uu____4008
                                                                    =
                                                                    let uu____4017
                                                                    =
                                                                    let uu____4018
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4018 in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4017,
                                                                    "Print the time it takes to verify each top-level definition") in
                                                                    let uu____4019
                                                                    =
                                                                    let uu____4030
                                                                    =
                                                                    let uu____4039
                                                                    =
                                                                    let uu____4040
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4040 in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4039,
                                                                    "Don't print an error message; show an exception trace instead") in
                                                                    let uu____4041
                                                                    =
                                                                    let uu____4052
                                                                    =
                                                                    let uu____4061
                                                                    =
                                                                    let uu____4062
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4062 in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4061,
                                                                    "Emit output formatted for debugging") in
                                                                    let uu____4063
                                                                    =
                                                                    let uu____4074
                                                                    =
                                                                    let uu____4083
                                                                    =
                                                                    let uu____4084
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4084 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4083,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)") in
                                                                    let uu____4085
                                                                    =
                                                                    let uu____4096
                                                                    =
                                                                    let uu____4105
                                                                    =
                                                                    let uu____4106
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4106 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4105,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.") in
                                                                    let uu____4107
                                                                    =
                                                                    let uu____4118
                                                                    =
                                                                    let uu____4127
                                                                    =
                                                                    let uu____4128
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4128 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4127,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)") in
                                                                    let uu____4129
                                                                    =
                                                                    let uu____4140
                                                                    =
                                                                    let uu____4149
                                                                    =
                                                                    let uu____4150
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4150 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4149,
                                                                    "Use a previously recorded hints database for proof replay") in
                                                                    let uu____4151
                                                                    =
                                                                    let uu____4162
                                                                    =
                                                                    let uu____4171
                                                                    =
                                                                    let uu____4172
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4172 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4171,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database") in
                                                                    let uu____4173
                                                                    =
                                                                    let uu____4184
                                                                    =
                                                                    let uu____4195
                                                                    =
                                                                    let uu____4204
                                                                    =
                                                                    let uu____4205
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4205 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4204,
                                                                    "Do not run the tactic engine before discharging a VC") in
                                                                    let uu____4206
                                                                    =
                                                                    let uu____4217
                                                                    =
                                                                    let uu____4228
                                                                    =
                                                                    let uu____4237
                                                                    =
                                                                    let uu____4238
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4238 in
                                                                    (FStar_Getopt.noshort,
                                                                    "verify_all",
                                                                    uu____4237,
                                                                    "With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.") in
                                                                    let uu____4239
                                                                    =
                                                                    let uu____4250
                                                                    =
                                                                    let uu____4261
                                                                    =
                                                                    let uu____4272
                                                                    =
                                                                    let uu____4281
                                                                    =
                                                                    let uu____4282
                                                                    =
                                                                    let uu____4289
                                                                    =
                                                                    let uu____4290
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4290 in
                                                                    ((fun
                                                                    uu____4295
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____4289) in
                                                                    WithSideEffect
                                                                    uu____4282 in
                                                                    (118,
                                                                    "version",
                                                                    uu____4281,
                                                                    "Display version number") in
                                                                    let uu____4297
                                                                    =
                                                                    let uu____4308
                                                                    =
                                                                    let uu____4317
                                                                    =
                                                                    let uu____4318
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4318 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4317,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)") in
                                                                    let uu____4319
                                                                    =
                                                                    let uu____4330
                                                                    =
                                                                    let uu____4341
                                                                    =
                                                                    let uu____4350
                                                                    =
                                                                    let uu____4351
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4351 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4350,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness") in
                                                                    let uu____4352
                                                                    =
                                                                    let uu____4363
                                                                    =
                                                                    let uu____4374
                                                                    =
                                                                    let uu____4385
                                                                    =
                                                                    let uu____4396
                                                                    =
                                                                    let uu____4405
                                                                    =
                                                                    let uu____4406
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4406 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4405,
                                                                    "Don't check positivity of inductive types") in
                                                                    let uu____4407
                                                                    =
                                                                    let uu____4418
                                                                    =
                                                                    let uu____4427
                                                                    =
                                                                    let uu____4428
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4428 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4427,
                                                                    "Do not eta-expand coertions in generated OCaml") in
                                                                    let uu____4429
                                                                    =
                                                                    let uu____4440
                                                                    =
                                                                    let uu____4449
                                                                    =
                                                                    let uu____4450
                                                                    =
                                                                    let uu____4457
                                                                    =
                                                                    let uu____4458
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4458 in
                                                                    ((fun
                                                                    uu____4463
                                                                     ->
                                                                    (
                                                                    let uu____4465
                                                                    =
                                                                    specs () in
                                                                    display_usage_aux
                                                                    uu____4465);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____4457) in
                                                                    WithSideEffect
                                                                    uu____4450 in
                                                                    (104,
                                                                    "help",
                                                                    uu____4449,
                                                                    "Display this information") in
                                                                    [uu____4440] in
                                                                    uu____4418
                                                                    ::
                                                                    uu____4429 in
                                                                    uu____4396
                                                                    ::
                                                                    uu____4407 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4385 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4374 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4363 in
                                                                    uu____4341
                                                                    ::
                                                                    uu____4352 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4330 in
                                                                    uu____4308
                                                                    ::
                                                                    uu____4319 in
                                                                    uu____4272
                                                                    ::
                                                                    uu____4297 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4261 in
                                                                    (FStar_Getopt.noshort,
                                                                    "verify_module",
                                                                    (Accumulated
                                                                    (PostProcessed
                                                                    (pp_lowercase,
                                                                    (SimpleStr
                                                                    "module_name")))),
                                                                    "Name of the module to verify")
                                                                    ::
                                                                    uu____4250 in
                                                                    uu____4228
                                                                    ::
                                                                    uu____4239 in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4217 in
                                                                    uu____4195
                                                                    ::
                                                                    uu____4206 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4184 in
                                                                    uu____4162
                                                                    ::
                                                                    uu____4173 in
                                                                    uu____4140
                                                                    ::
                                                                    uu____4151 in
                                                                    uu____4118
                                                                    ::
                                                                    uu____4129 in
                                                                    uu____4096
                                                                    ::
                                                                    uu____4107 in
                                                                    uu____4074
                                                                    ::
                                                                    uu____4085 in
                                                                    uu____4052
                                                                    ::
                                                                    uu____4063 in
                                                                    uu____4030
                                                                    ::
                                                                    uu____4041 in
                                                                    uu____4008
                                                                    ::
                                                                    uu____4019 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3997 in
                                                                    uu____3975
                                                                    ::
                                                                    uu____3986 in
                                                                    (FStar_Getopt.noshort,
                                                                    "split_cases",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Partition VC of a match into groups of <positive_integer> cases")
                                                                    ::
                                                                    uu____3964 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3953 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3942 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3931 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3920 in
                                                                    uu____3898
                                                                    ::
                                                                    uu____3909 in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3887 in
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
                                                                    uu____3777
                                                                    ::
                                                                    uu____3788 in
                                                                    uu____3755
                                                                    ::
                                                                    uu____3766 in
                                                                    uu____3733
                                                                    ::
                                                                    uu____3744 in
                                                                    uu____3711
                                                                    ::
                                                                    uu____3722 in
                                                                    uu____3689
                                                                    ::
                                                                    uu____3700 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3678 in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3667 in
                                                                    uu____3645
                                                                    ::
                                                                    uu____3656 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Do not extract code from this module")
                                                                    ::
                                                                    uu____3634 in
                                                                    uu____3612
                                                                    ::
                                                                    uu____3623 in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3601 in
                                                                    uu____3579
                                                                    ::
                                                                    uu____3590 in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3568 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3557 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3546 in
                                                                  uu____3524
                                                                    ::
                                                                    uu____3535 in
                                                                uu____3502 ::
                                                                  uu____3513 in
                                                              (FStar_Getopt.noshort,
                                                                "load",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "module")),
                                                                "Load compiled module")
                                                                :: uu____3491 in
                                                            uu____3469 ::
                                                              uu____3480 in
                                                          (FStar_Getopt.noshort,
                                                            "initial_ifuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                            :: uu____3458 in
                                                        (FStar_Getopt.noshort,
                                                          "initial_fuel",
                                                          (IntStr
                                                             "non-negative integer"),
                                                          "Number of unrolling of recursive functions to try initially (default 2)")
                                                          :: uu____3447 in
                                                      uu____3425 ::
                                                        uu____3436 in
                                                    (FStar_Getopt.noshort,
                                                      "include",
                                                      (ReverseAccumulated
                                                         (PathStr "path")),
                                                      "A directory in which to search for files included on the command line")
                                                      :: uu____3414 in
                                                  uu____3392 :: uu____3403 in
                                                uu____3370 :: uu____3381 in
                                              uu____3348 :: uu____3359 in
                                            (FStar_Getopt.noshort,
                                              "hint_file", (PathStr "path"),
                                              "Read/write hints to <path> (instead of module-specific hints files)")
                                              :: uu____3337 in
                                          uu____3315 :: uu____3326 in
                                        (FStar_Getopt.noshort,
                                          "gen_native_tactics",
                                          (PathStr "[path]"),
                                          "Compile all user tactics used in the module in <path>")
                                          :: uu____3304 in
                                      (FStar_Getopt.noshort, "fstar_home",
                                        (PathStr "dir"),
                                        "Set the FSTAR_HOME variable to <dir>")
                                        :: uu____3293 in
                                    (FStar_Getopt.noshort,
                                      "extract_namespace",
                                      (Accumulated
                                         (PostProcessed
                                            (pp_lowercase,
                                              (SimpleStr "namespace name")))),
                                      "Only extract modules in the specified namespace")
                                      :: uu____3282 in
                                  (FStar_Getopt.noshort, "extract_module",
                                    (Accumulated
                                       (PostProcessed
                                          (pp_lowercase,
                                            (SimpleStr "module_name")))),
                                    "Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                    :: uu____3271 in
                                uu____3249 :: uu____3260 in
                              uu____3227 :: uu____3238 in
                            uu____3205 :: uu____3216 in
                          (FStar_Getopt.noshort, "dump_module",
                            (Accumulated (SimpleStr "module_name")), "") ::
                            uu____3194 in
                        uu____3172 :: uu____3183 in
                      uu____3150 :: uu____3161 in
                    uu____3128 :: uu____3139 in
                  (FStar_Getopt.noshort, "dep", (EnumStr ["make"; "graph"]),
                    "Output the transitive closure of the dependency graph in a format suitable for the given tool")
                    :: uu____3117 in
                (FStar_Getopt.noshort, "debug_level",
                  (Accumulated
                     (OpenEnumStr
                        (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                  "Control the verbosity of debugging info") :: uu____3106 in
              (FStar_Getopt.noshort, "debug",
                (Accumulated (SimpleStr "module_name")),
                "Print lots of debugging information while checking module")
                :: uu____3095 in
            (FStar_Getopt.noshort, "codegen-lib",
              (Accumulated (SimpleStr "namespace")),
              "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
              :: uu____3084 in
          (FStar_Getopt.noshort, "codegen",
            (EnumStr ["OCaml"; "FSharp"; "Kremlin"]),
            "Generate code for execution") :: uu____3073 in
        uu____3051 :: uu____3062 in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____3040 in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____3029
and specs: Prims.unit -> FStar_Getopt.opt Prims.list =
  fun uu____5168  ->
    let uu____5171 = specs_with_types () in
    FStar_List.map
      (fun uu____5196  ->
         match uu____5196 with
         | (short,long,typ,doc) ->
             let uu____5209 =
               let uu____5220 = arg_spec_of_opt_type long typ in
               (short, long, uu____5220, doc) in
             mk_spec uu____5209) uu____5171
let settable: Prims.string -> Prims.bool =
  fun uu___65_5228  ->
    match uu___65_5228 with
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
    | uu____5229 -> false
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
       (fun uu____5287  ->
          match uu____5287 with
          | (uu____5298,x,uu____5300,uu____5301) -> settable x))
let resettable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5347  ->
          match uu____5347 with
          | (uu____5358,x,uu____5360,uu____5361) -> resettable x))
let display_usage: Prims.unit -> Prims.unit =
  fun uu____5369  ->
    let uu____5370 = specs () in display_usage_aux uu____5370
let fstar_home: Prims.unit -> Prims.string =
  fun uu____5386  ->
    let uu____5387 = get_fstar_home () in
    match uu____5387 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        ((let uu____5393 =
            let uu____5398 = mk_string x1 in ("fstar_home", uu____5398) in
          set_option' uu____5393);
         x1)
    | FStar_Pervasives_Native.Some x -> x
exception File_argument of Prims.string
let uu___is_File_argument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____5407 -> true
    | uu____5408 -> false
let __proj__File_argument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____5416 -> uu____5416
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
          let uu____5462 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____5462
let file_list_: Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let parse_cmd_line:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____5485  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5490 =
             let uu____5493 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____5493 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____5490) in
    let uu____5596 =
      let uu____5599 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5599 in
    (res, uu____5596)
let file_list: Prims.unit -> Prims.string Prims.list =
  fun uu____5659  -> FStar_ST.op_Bang file_list_
let restore_cmd_line_options: Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____5720 = specs () in
       FStar_Getopt.parse_cmdline uu____5720 (fun x  -> ()) in
     (let uu____5726 =
        let uu____5731 =
          let uu____5732 = FStar_List.map mk_string old_verify_module in
          List uu____5732 in
        ("verify_module", uu____5731) in
      set_option' uu____5726);
     r)
let module_name_of_file_name: Prims.string -> Prims.string =
  fun f  ->
    let f1 = FStar_Util.basename f in
    let f2 =
      let uu____5741 =
        let uu____5742 =
          let uu____5743 =
            let uu____5744 = FStar_Util.get_file_extension f1 in
            FStar_String.length uu____5744 in
          (FStar_String.length f1) - uu____5743 in
        uu____5742 - (Prims.parse_int "1") in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5741 in
    FStar_String.lowercase f2
let should_verify: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5749 = get_lax () in
    if uu____5749
    then false
    else
      (let uu____5751 = get_verify_all () in
       if uu____5751
       then true
       else
         (let uu____5753 = get_verify_module () in
          match uu____5753 with
          | [] ->
              let uu____5756 = file_list () in
              FStar_List.existsML
                (fun f  ->
                   let uu____5762 = module_name_of_file_name f in
                   uu____5762 = m) uu____5756
          | l -> FStar_List.contains (FStar_String.lowercase m) l))
let should_verify_file: Prims.string -> Prims.bool =
  fun fn  ->
    let uu____5770 = module_name_of_file_name fn in should_verify uu____5770
let dont_gen_projectors: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5775 = get___temp_no_proj () in
    FStar_List.contains m uu____5775
let should_print_message: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5782 = should_verify m in
    if uu____5782 then m <> "Prims" else false
let include_path: Prims.unit -> Prims.string Prims.list =
  fun uu____5789  ->
    let uu____5790 = get_no_default_includes () in
    if uu____5790
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____5798 =
         let uu____5801 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____5801
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____5814 =
         let uu____5817 = get_include () in
         FStar_List.append uu____5817 ["."] in
       FStar_List.append uu____5798 uu____5814)
let find_file: Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____5826 = FStar_Util.is_path_absolute filename in
    if uu____5826
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5833 =
         let uu____5836 = include_path () in FStar_List.rev uu____5836 in
       FStar_Util.find_map uu____5833
         (fun p  ->
            let path = FStar_Util.join_paths p filename in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
let prims: Prims.unit -> Prims.string =
  fun uu____5849  ->
    let uu____5850 = get_prims () in
    match uu____5850 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst" in
        let uu____5854 = find_file filename in
        (match uu____5854 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5858 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename in
             failwith uu____5858)
    | FStar_Pervasives_Native.Some x -> x
let prims_basename: Prims.unit -> Prims.string =
  fun uu____5863  ->
    let uu____5864 = prims () in FStar_Util.basename uu____5864
let pervasives: Prims.unit -> Prims.string =
  fun uu____5868  ->
    let filename = "FStar.Pervasives.fst" in
    let uu____5870 = find_file filename in
    match uu____5870 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5874 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5874
let pervasives_basename: Prims.unit -> Prims.string =
  fun uu____5878  ->
    let uu____5879 = pervasives () in FStar_Util.basename uu____5879
let pervasives_native_basename: Prims.unit -> Prims.string =
  fun uu____5883  ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____5885 = find_file filename in
    match uu____5885 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5889 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5889
let prepend_output_dir: Prims.string -> Prims.string =
  fun fname  ->
    let uu____5894 = get_odir () in
    match uu____5894 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
let __temp_no_proj: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5902 = get___temp_no_proj () in
    FStar_All.pipe_right uu____5902 (FStar_List.contains s)
let admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____5910  -> get_admit_smt_queries ()
let admit_except: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5916  -> get_admit_except ()
let cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____5920  -> get_cache_checked_modules ()
let codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5926  -> get_codegen ()
let codegen_libs: Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____5934  ->
    let uu____5935 = get_codegen_lib () in
    FStar_All.pipe_right uu____5935
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
let debug_any: Prims.unit -> Prims.bool =
  fun uu____5951  -> let uu____5952 = get_debug () in uu____5952 <> []
let debug_at_level: Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      (let uu____5967 = get_debug () in
       FStar_All.pipe_right uu____5967 (FStar_List.contains modul)) &&
        (debug_level_geq level)
let dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5977  -> get_dep ()
let detail_errors: Prims.unit -> Prims.bool =
  fun uu____5981  -> get_detail_errors ()
let detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____5985  -> get_detail_hint_replay ()
let doc: Prims.unit -> Prims.bool = fun uu____5989  -> get_doc ()
let dump_module: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5994 = get_dump_module () in
    FStar_All.pipe_right uu____5994 (FStar_List.contains s)
let eager_inference: Prims.unit -> Prims.bool =
  fun uu____6002  -> get_eager_inference ()
let explicit_deps: Prims.unit -> Prims.bool =
  fun uu____6006  -> get_explicit_deps ()
let extract_all: Prims.unit -> Prims.bool =
  fun uu____6010  -> get_extract_all ()
let fs_typ_app: Prims.string -> Prims.bool =
  fun filename  ->
    let uu____6015 = FStar_ST.op_Bang light_off_files in
    FStar_List.contains filename uu____6015
let gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____6073  -> get_gen_native_tactics ()
let full_context_dependency: Prims.unit -> Prims.bool =
  fun uu____6077  -> true
let hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____6081  -> get_hide_uvar_nums ()
let hint_info: Prims.unit -> Prims.bool =
  fun uu____6085  -> (get_hint_info ()) || (get_query_stats ())
let hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____6091  -> get_hint_file ()
let ide: Prims.unit -> Prims.bool = fun uu____6095  -> get_ide ()
let indent: Prims.unit -> Prims.bool = fun uu____6099  -> get_indent ()
let initial_fuel: Prims.unit -> Prims.int =
  fun uu____6103  ->
    let uu____6104 = get_initial_fuel () in
    let uu____6105 = get_max_fuel () in Prims.min uu____6104 uu____6105
let initial_ifuel: Prims.unit -> Prims.int =
  fun uu____6109  ->
    let uu____6110 = get_initial_ifuel () in
    let uu____6111 = get_max_ifuel () in Prims.min uu____6110 uu____6111
let interactive: Prims.unit -> Prims.bool =
  fun uu____6115  -> (get_in ()) || (get_ide ())
let lax: Prims.unit -> Prims.bool = fun uu____6119  -> get_lax ()
let load: Prims.unit -> Prims.string Prims.list =
  fun uu____6125  -> get_load ()
let legacy_interactive: Prims.unit -> Prims.bool =
  fun uu____6129  -> get_in ()
let log_queries: Prims.unit -> Prims.bool =
  fun uu____6133  -> get_log_queries ()
let log_types: Prims.unit -> Prims.bool = fun uu____6137  -> get_log_types ()
let max_fuel: Prims.unit -> Prims.int = fun uu____6141  -> get_max_fuel ()
let max_ifuel: Prims.unit -> Prims.int = fun uu____6145  -> get_max_ifuel ()
let min_fuel: Prims.unit -> Prims.int = fun uu____6149  -> get_min_fuel ()
let ml_ish: Prims.unit -> Prims.bool = fun uu____6153  -> get_MLish ()
let set_ml_ish: Prims.unit -> Prims.unit =
  fun uu____6157  -> set_option "MLish" (Bool true)
let n_cores: Prims.unit -> Prims.int = fun uu____6161  -> get_n_cores ()
let no_default_includes: Prims.unit -> Prims.bool =
  fun uu____6165  -> get_no_default_includes ()
let no_extract: Prims.string -> Prims.bool =
  fun s  ->
    let uu____6170 = get_no_extract () in
    FStar_All.pipe_right uu____6170 (FStar_List.contains s)
let no_location_info: Prims.unit -> Prims.bool =
  fun uu____6178  -> get_no_location_info ()
let output_dir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____6184  -> get_odir ()
let ugly: Prims.unit -> Prims.bool = fun uu____6188  -> get_ugly ()
let print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____6192  -> get_print_bound_var_types ()
let print_effect_args: Prims.unit -> Prims.bool =
  fun uu____6196  -> get_print_effect_args ()
let print_implicits: Prims.unit -> Prims.bool =
  fun uu____6200  -> get_print_implicits ()
let print_real_names: Prims.unit -> Prims.bool =
  fun uu____6204  -> (get_prn ()) || (get_print_full_names ())
let print_universes: Prims.unit -> Prims.bool =
  fun uu____6208  -> get_print_universes ()
let print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____6212  -> (get_print_z3_statistics ()) || (get_query_stats ())
let query_stats: Prims.unit -> Prims.bool =
  fun uu____6216  -> get_query_stats ()
let record_hints: Prims.unit -> Prims.bool =
  fun uu____6220  -> get_record_hints ()
let reuse_hint_for: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____6226  -> get_reuse_hint_for ()
let silent: Prims.unit -> Prims.bool = fun uu____6230  -> get_silent ()
let smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____6234  -> get_smtencoding_elim_box ()
let smtencoding_nl_arith_native: Prims.unit -> Prims.bool =
  fun uu____6238  ->
    let uu____6239 = get_smtencoding_nl_arith_repr () in
    uu____6239 = "native"
let smtencoding_nl_arith_wrapped: Prims.unit -> Prims.bool =
  fun uu____6243  ->
    let uu____6244 = get_smtencoding_nl_arith_repr () in
    uu____6244 = "wrapped"
let smtencoding_nl_arith_default: Prims.unit -> Prims.bool =
  fun uu____6248  ->
    let uu____6249 = get_smtencoding_nl_arith_repr () in
    uu____6249 = "boxwrap"
let smtencoding_l_arith_native: Prims.unit -> Prims.bool =
  fun uu____6253  ->
    let uu____6254 = get_smtencoding_l_arith_repr () in uu____6254 = "native"
let smtencoding_l_arith_default: Prims.unit -> Prims.bool =
  fun uu____6258  ->
    let uu____6259 = get_smtencoding_l_arith_repr () in
    uu____6259 = "boxwrap"
let split_cases: Prims.unit -> Prims.int =
  fun uu____6263  -> get_split_cases ()
let tactic_trace: Prims.unit -> Prims.bool =
  fun uu____6267  -> get_tactic_trace ()
let tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____6271  -> get_tactic_trace_d ()
let timing: Prims.unit -> Prims.bool = fun uu____6275  -> get_timing ()
let trace_error: Prims.unit -> Prims.bool =
  fun uu____6279  -> get_trace_error ()
let unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____6283  -> get_unthrottle_inductives ()
let unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____6287  -> get_unsafe_tactic_exec ()
let use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____6291  -> get_use_eq_at_higher_order ()
let use_hints: Prims.unit -> Prims.bool = fun uu____6295  -> get_use_hints ()
let use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____6299  -> get_use_hint_hashes ()
let use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____6305  -> get_use_native_tactics ()
let use_tactics: Prims.unit -> Prims.bool =
  fun uu____6309  -> get_use_tactics ()
let using_facts_from:
  Prims.unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____6319  ->
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if FStar_Util.starts_with s "-"
        then
          (let path =
             let uu____6348 =
               FStar_Util.substring_from s (Prims.parse_int "1") in
             FStar_Ident.path_of_text uu____6348 in
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
    let uu____6384 = get_using_facts_from () in
    match uu____6384 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns ->
        let uu____6416 = FStar_List.collect parse_setting ns in
        FStar_All.pipe_right uu____6416 FStar_List.rev
let verify_all: Prims.unit -> Prims.bool =
  fun uu____6456  -> get_verify_all ()
let verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____6462  -> get_verify_module ()
let warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____6466  -> get_warn_default_effects ()
let z3_exe: Prims.unit -> Prims.string =
  fun uu____6470  ->
    let uu____6471 = get_smt () in
    match uu____6471 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let z3_cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____6480  -> get_z3cliopt ()
let z3_refresh: Prims.unit -> Prims.bool =
  fun uu____6484  -> get_z3refresh ()
let z3_rlimit: Prims.unit -> Prims.int = fun uu____6488  -> get_z3rlimit ()
let z3_rlimit_factor: Prims.unit -> Prims.int =
  fun uu____6492  -> get_z3rlimit_factor ()
let z3_seed: Prims.unit -> Prims.int = fun uu____6496  -> get_z3seed ()
let no_positivity: Prims.unit -> Prims.bool =
  fun uu____6500  -> get_no_positivity ()
let ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____6504  -> get_ml_no_eta_expand_coertions ()
let should_extract: Prims.string -> Prims.bool =
  fun m  ->
    (let uu____6511 = no_extract m in Prims.op_Negation uu____6511) &&
      ((extract_all ()) ||
         (let uu____6514 = get_extract_module () in
          match uu____6514 with
          | [] ->
              let uu____6517 = get_extract_namespace () in
              (match uu____6517 with
               | [] -> true
               | ns ->
                   FStar_Util.for_some
                     (FStar_Util.starts_with (FStar_String.lowercase m)) ns)
          | l -> FStar_List.contains (FStar_String.lowercase m) l))
let codegen_fsharp: Prims.unit -> Prims.bool =
  fun uu____6529  ->
    let uu____6530 = codegen () in
    uu____6530 = (FStar_Pervasives_Native.Some "FSharp")