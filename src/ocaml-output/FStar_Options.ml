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
  fun uu___48_338  ->
    match uu___48_338 with
    | Bool b -> b
    | uu____340 -> failwith "Impos: expected Bool"
let as_int: option_val -> Prims.int =
  fun uu___49_344  ->
    match uu___49_344 with
    | Int b -> b
    | uu____346 -> failwith "Impos: expected Int"
let as_string: option_val -> Prims.string =
  fun uu___50_350  ->
    match uu___50_350 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____353 -> failwith "Impos: expected String"
let as_list': option_val -> option_val Prims.list =
  fun uu___51_359  ->
    match uu___51_359 with
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
    fun uu___52_416  ->
      match uu___52_416 with
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
  ("_fstar_home", (String ""));
  ("_include_path", (List []));
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
  ("hide_genident_nums", (Bool false));
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
  ("show_signatures", (List []));
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
  fun uu____1378  ->
    let o = peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let clear: Prims.unit -> Prims.unit =
  fun uu____1394  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50") in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
let _run: Prims.unit = clear ()
let get_option: Prims.string -> option_val =
  fun s  ->
    let uu____1508 =
      let uu____1511 = peek () in FStar_Util.smap_try_find uu____1511 s in
    match uu____1508 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
let lookup_opt:
  'Auu____1521 . Prims.string -> (option_val -> 'Auu____1521) -> 'Auu____1521
  = fun s  -> fun c  -> c (get_option s)
let get_admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____1538  -> lookup_opt "admit_smt_queries" as_bool
let get_admit_except:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1544  -> lookup_opt "admit_except" (as_option as_string)
let get_cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____1550  -> lookup_opt "cache_checked_modules" as_bool
let get_codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1556  -> lookup_opt "codegen" (as_option as_string)
let get_codegen_lib: Prims.unit -> Prims.string Prims.list =
  fun uu____1564  -> lookup_opt "codegen-lib" (as_list as_string)
let get_debug: Prims.unit -> Prims.string Prims.list =
  fun uu____1572  -> lookup_opt "debug" (as_list as_string)
let get_debug_level: Prims.unit -> Prims.string Prims.list =
  fun uu____1580  -> lookup_opt "debug_level" (as_list as_string)
let get_dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1588  -> lookup_opt "dep" (as_option as_string)
let get_detail_errors: Prims.unit -> Prims.bool =
  fun uu____1594  -> lookup_opt "detail_errors" as_bool
let get_detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____1598  -> lookup_opt "detail_hint_replay" as_bool
let get_doc: Prims.unit -> Prims.bool =
  fun uu____1602  -> lookup_opt "doc" as_bool
let get_dump_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1608  -> lookup_opt "dump_module" (as_list as_string)
let get_eager_inference: Prims.unit -> Prims.bool =
  fun uu____1614  -> lookup_opt "eager_inference" as_bool
let get_explicit_deps: Prims.unit -> Prims.bool =
  fun uu____1618  -> lookup_opt "explicit_deps" as_bool
let get_extract_all: Prims.unit -> Prims.bool =
  fun uu____1622  -> lookup_opt "extract_all" as_bool
let get_extract_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1628  -> lookup_opt "extract_module" (as_list as_string)
let get_extract_namespace: Prims.unit -> Prims.string Prims.list =
  fun uu____1636  -> lookup_opt "extract_namespace" (as_list as_string)
let get_fs_typ_app: Prims.unit -> Prims.bool =
  fun uu____1642  -> lookup_opt "fs_typ_app" as_bool
let get_fstar_home: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1648  -> lookup_opt "fstar_home" (as_option as_string)
let get_gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1656  -> lookup_opt "gen_native_tactics" (as_option as_string)
let get_hide_genident_nums: Prims.unit -> Prims.bool =
  fun uu____1662  -> lookup_opt "hide_genident_nums" as_bool
let get_hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____1666  -> lookup_opt "hide_uvar_nums" as_bool
let get_hint_info: Prims.unit -> Prims.bool =
  fun uu____1670  -> lookup_opt "hint_info" as_bool
let get_hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1676  -> lookup_opt "hint_file" (as_option as_string)
let get_in: Prims.unit -> Prims.bool =
  fun uu____1682  -> lookup_opt "in" as_bool
let get_ide: Prims.unit -> Prims.bool =
  fun uu____1686  -> lookup_opt "ide" as_bool
let get_include: Prims.unit -> Prims.string Prims.list =
  fun uu____1692  -> lookup_opt "include" (as_list as_string)
let get_indent: Prims.unit -> Prims.bool =
  fun uu____1698  -> lookup_opt "indent" as_bool
let get_initial_fuel: Prims.unit -> Prims.int =
  fun uu____1702  -> lookup_opt "initial_fuel" as_int
let get_initial_ifuel: Prims.unit -> Prims.int =
  fun uu____1706  -> lookup_opt "initial_ifuel" as_int
let get_lax: Prims.unit -> Prims.bool =
  fun uu____1710  -> lookup_opt "lax" as_bool
let get_load: Prims.unit -> Prims.string Prims.list =
  fun uu____1716  -> lookup_opt "load" (as_list as_string)
let get_log_queries: Prims.unit -> Prims.bool =
  fun uu____1722  -> lookup_opt "log_queries" as_bool
let get_log_types: Prims.unit -> Prims.bool =
  fun uu____1726  -> lookup_opt "log_types" as_bool
let get_max_fuel: Prims.unit -> Prims.int =
  fun uu____1730  -> lookup_opt "max_fuel" as_int
let get_max_ifuel: Prims.unit -> Prims.int =
  fun uu____1734  -> lookup_opt "max_ifuel" as_int
let get_min_fuel: Prims.unit -> Prims.int =
  fun uu____1738  -> lookup_opt "min_fuel" as_int
let get_MLish: Prims.unit -> Prims.bool =
  fun uu____1742  -> lookup_opt "MLish" as_bool
let get_n_cores: Prims.unit -> Prims.int =
  fun uu____1746  -> lookup_opt "n_cores" as_int
let get_no_default_includes: Prims.unit -> Prims.bool =
  fun uu____1750  -> lookup_opt "no_default_includes" as_bool
let get_no_extract: Prims.unit -> Prims.string Prims.list =
  fun uu____1756  -> lookup_opt "no_extract" (as_list as_string)
let get_no_location_info: Prims.unit -> Prims.bool =
  fun uu____1762  -> lookup_opt "no_location_info" as_bool
let get_odir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1768  -> lookup_opt "odir" (as_option as_string)
let get_ugly: Prims.unit -> Prims.bool =
  fun uu____1774  -> lookup_opt "ugly" as_bool
let get_prims: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1780  -> lookup_opt "prims" (as_option as_string)
let get_print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____1786  -> lookup_opt "print_bound_var_types" as_bool
let get_print_effect_args: Prims.unit -> Prims.bool =
  fun uu____1790  -> lookup_opt "print_effect_args" as_bool
let get_print_full_names: Prims.unit -> Prims.bool =
  fun uu____1794  -> lookup_opt "print_full_names" as_bool
let get_print_implicits: Prims.unit -> Prims.bool =
  fun uu____1798  -> lookup_opt "print_implicits" as_bool
let get_print_universes: Prims.unit -> Prims.bool =
  fun uu____1802  -> lookup_opt "print_universes" as_bool
let get_print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____1806  -> lookup_opt "print_z3_statistics" as_bool
let get_prn: Prims.unit -> Prims.bool =
  fun uu____1810  -> lookup_opt "prn" as_bool
let get_query_stats: Prims.unit -> Prims.bool =
  fun uu____1814  -> lookup_opt "query_stats" as_bool
let get_record_hints: Prims.unit -> Prims.bool =
  fun uu____1818  -> lookup_opt "record_hints" as_bool
let get_reuse_hint_for:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1824  -> lookup_opt "reuse_hint_for" (as_option as_string)
let get_show_signatures: Prims.unit -> Prims.string Prims.list =
  fun uu____1832  -> lookup_opt "show_signatures" (as_list as_string)
let get_silent: Prims.unit -> Prims.bool =
  fun uu____1838  -> lookup_opt "silent" as_bool
let get_smt: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1844  -> lookup_opt "smt" (as_option as_string)
let get_smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____1850  -> lookup_opt "smtencoding.elim_box" as_bool
let get_smtencoding_nl_arith_repr: Prims.unit -> Prims.string =
  fun uu____1854  -> lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr: Prims.unit -> Prims.string =
  fun uu____1858  -> lookup_opt "smtencoding.l_arith_repr" as_string
let get_split_cases: Prims.unit -> Prims.int =
  fun uu____1862  -> lookup_opt "split_cases" as_int
let get_tactic_trace: Prims.unit -> Prims.bool =
  fun uu____1866  -> lookup_opt "tactic_trace" as_bool
let get_tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____1870  -> lookup_opt "tactic_trace_d" as_int
let get_timing: Prims.unit -> Prims.bool =
  fun uu____1874  -> lookup_opt "timing" as_bool
let get_trace_error: Prims.unit -> Prims.bool =
  fun uu____1878  -> lookup_opt "trace_error" as_bool
let get_unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____1882  -> lookup_opt "unthrottle_inductives" as_bool
let get_unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____1886  -> lookup_opt "unsafe_tactic_exec" as_bool
let get_use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____1890  -> lookup_opt "use_eq_at_higher_order" as_bool
let get_use_hints: Prims.unit -> Prims.bool =
  fun uu____1894  -> lookup_opt "use_hints" as_bool
let get_use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____1898  -> lookup_opt "use_hint_hashes" as_bool
let get_use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1904  -> lookup_opt "use_native_tactics" (as_option as_string)
let get_use_tactics: Prims.unit -> Prims.bool =
  fun uu____1910  ->
    let uu____1911 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____1911
let get_using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1919  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let get_verify_all: Prims.unit -> Prims.bool =
  fun uu____1929  -> lookup_opt "verify_all" as_bool
let get_verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1935  -> lookup_opt "verify_module" (as_list as_string)
let get___temp_no_proj: Prims.unit -> Prims.string Prims.list =
  fun uu____1943  -> lookup_opt "__temp_no_proj" (as_list as_string)
let get_version: Prims.unit -> Prims.bool =
  fun uu____1949  -> lookup_opt "version" as_bool
let get_warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____1953  -> lookup_opt "warn_default_effects" as_bool
let get_z3cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____1959  -> lookup_opt "z3cliopt" (as_list as_string)
let get_z3refresh: Prims.unit -> Prims.bool =
  fun uu____1965  -> lookup_opt "z3refresh" as_bool
let get_z3rlimit: Prims.unit -> Prims.int =
  fun uu____1969  -> lookup_opt "z3rlimit" as_int
let get_z3rlimit_factor: Prims.unit -> Prims.int =
  fun uu____1973  -> lookup_opt "z3rlimit_factor" as_int
let get_z3seed: Prims.unit -> Prims.int =
  fun uu____1977  -> lookup_opt "z3seed" as_int
let get_no_positivity: Prims.unit -> Prims.bool =
  fun uu____1981  -> lookup_opt "__no_positivity" as_bool
let get_ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____1985  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool
let dlevel: Prims.string -> debug_level_t =
  fun uu___53_1989  ->
    match uu___53_1989 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let one_debug_level_geq: debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1999 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let debug_level_geq: debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____2004 = get_debug_level () in
    FStar_All.pipe_right uu____2004
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
let universe_include_path_base_dirs: Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"]
let _version: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _platform: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _compiler: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _date: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _commit: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let display_version: Prims.unit -> Prims.unit =
  fun uu____2096  ->
    let uu____2097 =
      let uu____2098 = FStar_ST.op_Bang _version in
      let uu____2145 = FStar_ST.op_Bang _platform in
      let uu____2192 = FStar_ST.op_Bang _compiler in
      let uu____2239 = FStar_ST.op_Bang _date in
      let uu____2286 = FStar_ST.op_Bang _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2098
        uu____2145 uu____2192 uu____2239 uu____2286 in
    FStar_Util.print_string uu____2097
let display_usage_aux:
  'Auu____2339 'Auu____2340 .
    ('Auu____2340,Prims.string,'Auu____2339 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2387  ->
         match uu____2387 with
         | (uu____2398,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2409 =
                      let uu____2410 = FStar_Util.colorize_bold flag in
                      FStar_Util.format1 "  --%s\n" uu____2410 in
                    FStar_Util.print_string uu____2409
                  else
                    (let uu____2412 =
                       let uu____2413 = FStar_Util.colorize_bold flag in
                       FStar_Util.format2 "  --%s  %s\n" uu____2413 doc in
                     FStar_Util.print_string uu____2412)
              | FStar_Getopt.OneArg (uu____2414,argname) ->
                  if doc = ""
                  then
                    let uu____2420 =
                      let uu____2421 = FStar_Util.colorize_bold flag in
                      let uu____2422 = FStar_Util.colorize_bold argname in
                      FStar_Util.format2 "  --%s %s\n" uu____2421 uu____2422 in
                    FStar_Util.print_string uu____2420
                  else
                    (let uu____2424 =
                       let uu____2425 = FStar_Util.colorize_bold flag in
                       let uu____2426 = FStar_Util.colorize_bold argname in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2425
                         uu____2426 doc in
                     FStar_Util.print_string uu____2424))) specs
let mk_spec:
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____2454 = o in
    match uu____2454 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2484 =
                let uu____2485 = f () in set_option name uu____2485 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2496 = f x in set_option name uu____2496 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2518 = lookup_opt name (as_option as_list') in
        FStar_Util.dflt [] uu____2518 in
      mk_list (value :: prev_values)
let reverse_accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let uu____2539 =
        let uu____2542 = lookup_opt name as_list' in
        FStar_List.append uu____2542 [value] in
      mk_list uu____2539
let accumulate_string:
  'Auu____2555 .
    Prims.string ->
      ('Auu____2555 -> Prims.string) -> 'Auu____2555 -> Prims.unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2573 =
          let uu____2574 =
            let uu____2575 = post_processor value in mk_string uu____2575 in
          accumulated_option name uu____2574 in
        set_option name uu____2573
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
    match projectee with | Const _0 -> true | uu____2657 -> false
let __proj__Const__item___0: opt_type -> option_val =
  fun projectee  -> match projectee with | Const _0 -> _0
let uu___is_IntStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2671 -> false
let __proj__IntStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | IntStr _0 -> _0
let uu___is_BoolStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2684 -> false
let uu___is_PathStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2690 -> false
let __proj__PathStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | PathStr _0 -> _0
let uu___is_SimpleStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2704 -> false
let __proj__SimpleStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0
let uu___is_EnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2720 -> false
let __proj__EnumStr__item___0: opt_type -> Prims.string Prims.list =
  fun projectee  -> match projectee with | EnumStr _0 -> _0
let uu___is_OpenEnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2746 -> false
let __proj__OpenEnumStr__item___0:
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0
let uu___is_PostProcessed: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2784 -> false
let __proj__PostProcessed__item___0:
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0
let uu___is_Accumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2816 -> false
let __proj__Accumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | Accumulated _0 -> _0
let uu___is_ReverseAccumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2830 -> false
let __proj__ReverseAccumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0
let uu___is_WithSideEffect: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2850 -> false
let __proj__WithSideEffect__item___0:
  opt_type ->
    (Prims.unit -> Prims.unit,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | WithSideEffect _0 -> _0
exception InvalidArgument of Prims.string
let uu___is_InvalidArgument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2884 -> true
    | uu____2885 -> false
let __proj__InvalidArgument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2893 -> uu____2893
let rec parse_opt_val: Prims.string -> opt_type -> Prims.string -> option_val
  =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2910 ->
              let uu____2911 = FStar_Util.safe_int_of_string str_val in
              (match uu____2911 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2915 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name) in
              mk_bool uu____2915
          | PathStr uu____2918 -> mk_path str_val
          | SimpleStr uu____2919 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2924 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2937 = parse_opt_val opt_name elem_spec str_val in
              pp uu____2937
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
            let uu____2954 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1 in
            failwith uu____2954
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
    | PostProcessed (uu____2988,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2996,elem_spec) -> desc_of_opt_type elem_spec
let rec arg_spec_of_opt_type:
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ in
      let uu____3017 = desc_of_opt_type typ in
      match uu____3017 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____3023  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
let pp_validate_dir: option_val -> option_val =
  fun p  -> let pp = as_string p in FStar_Util.mkdir false pp; p
let pp_lowercase: option_val -> option_val =
  fun s  ->
    let uu____3037 =
      let uu____3038 = as_string s in FStar_String.lowercase uu____3038 in
    mk_string uu____3037
let rec specs_with_types:
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun uu____3055  ->
    let uu____3066 =
      let uu____3077 =
        let uu____3088 =
          let uu____3097 = let uu____3098 = mk_bool true in Const uu____3098 in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____3097,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying") in
        let uu____3099 =
          let uu____3110 =
            let uu____3121 =
              let uu____3132 =
                let uu____3143 =
                  let uu____3154 =
                    let uu____3165 =
                      let uu____3174 =
                        let uu____3175 = mk_bool true in Const uu____3175 in
                      (FStar_Getopt.noshort, "detail_errors", uu____3174,
                        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1") in
                    let uu____3176 =
                      let uu____3187 =
                        let uu____3196 =
                          let uu____3197 = mk_bool true in Const uu____3197 in
                        (FStar_Getopt.noshort, "detail_hint_replay",
                          uu____3196,
                          "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1") in
                      let uu____3198 =
                        let uu____3209 =
                          let uu____3218 =
                            let uu____3219 = mk_bool true in Const uu____3219 in
                          (FStar_Getopt.noshort, "doc", uu____3218,
                            "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.") in
                        let uu____3220 =
                          let uu____3231 =
                            let uu____3242 =
                              let uu____3251 =
                                let uu____3252 = mk_bool true in
                                Const uu____3252 in
                              (FStar_Getopt.noshort, "eager_inference",
                                uu____3251,
                                "Solve all type-inference constraints eagerly; more efficient but at the cost of generality") in
                            let uu____3253 =
                              let uu____3264 =
                                let uu____3273 =
                                  let uu____3274 = mk_bool true in
                                  Const uu____3274 in
                                (FStar_Getopt.noshort, "explicit_deps",
                                  uu____3273,
                                  "Do not find dependencies automatically, the user provides them on the command-line") in
                              let uu____3275 =
                                let uu____3286 =
                                  let uu____3295 =
                                    let uu____3296 = mk_bool true in
                                    Const uu____3296 in
                                  (FStar_Getopt.noshort, "extract_all",
                                    uu____3295,
                                    "Discover the complete dependency graph and do not stop at interface boundaries") in
                                let uu____3297 =
                                  let uu____3308 =
                                    let uu____3319 =
                                      let uu____3330 =
                                        let uu____3341 =
                                          let uu____3352 =
                                            let uu____3361 =
                                              let uu____3362 = mk_bool true in
                                              Const uu____3362 in
                                            (FStar_Getopt.noshort,
                                              "hide_genident_nums",
                                              uu____3361,
                                              "Don't print generated identifier numbers") in
                                          let uu____3363 =
                                            let uu____3374 =
                                              let uu____3383 =
                                                let uu____3384 = mk_bool true in
                                                Const uu____3384 in
                                              (FStar_Getopt.noshort,
                                                "hide_uvar_nums", uu____3383,
                                                "Don't print unification variable numbers") in
                                            let uu____3385 =
                                              let uu____3396 =
                                                let uu____3407 =
                                                  let uu____3416 =
                                                    let uu____3417 =
                                                      mk_bool true in
                                                    Const uu____3417 in
                                                  (FStar_Getopt.noshort,
                                                    "hint_info", uu____3416,
                                                    "Print information regarding hints (deprecated; use --query_stats instead)") in
                                                let uu____3418 =
                                                  let uu____3429 =
                                                    let uu____3438 =
                                                      let uu____3439 =
                                                        mk_bool true in
                                                      Const uu____3439 in
                                                    (FStar_Getopt.noshort,
                                                      "in", uu____3438,
                                                      "Legacy interactive mode; reads input from stdin") in
                                                  let uu____3440 =
                                                    let uu____3451 =
                                                      let uu____3460 =
                                                        let uu____3461 =
                                                          mk_bool true in
                                                        Const uu____3461 in
                                                      (FStar_Getopt.noshort,
                                                        "ide", uu____3460,
                                                        "JSON-based interactive mode for IDEs") in
                                                    let uu____3462 =
                                                      let uu____3473 =
                                                        let uu____3484 =
                                                          let uu____3493 =
                                                            let uu____3494 =
                                                              mk_bool true in
                                                            Const uu____3494 in
                                                          (FStar_Getopt.noshort,
                                                            "indent",
                                                            uu____3493,
                                                            "Parses and outputs the files on the command line") in
                                                        let uu____3495 =
                                                          let uu____3506 =
                                                            let uu____3517 =
                                                              let uu____3528
                                                                =
                                                                let uu____3537
                                                                  =
                                                                  let uu____3538
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                  Const
                                                                    uu____3538 in
                                                                (FStar_Getopt.noshort,
                                                                  "lax",
                                                                  uu____3537,
                                                                  "Run the lax-type checker only (admit all verification conditions)") in
                                                              let uu____3539
                                                                =
                                                                let uu____3550
                                                                  =
                                                                  let uu____3561
                                                                    =
                                                                    let uu____3570
                                                                    =
                                                                    let uu____3571
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3571 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3570,
                                                                    "Print types computed for data/val/let-bindings") in
                                                                  let uu____3572
                                                                    =
                                                                    let uu____3583
                                                                    =
                                                                    let uu____3592
                                                                    =
                                                                    let uu____3593
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3593 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3592,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go") in
                                                                    let uu____3594
                                                                    =
                                                                    let uu____3605
                                                                    =
                                                                    let uu____3616
                                                                    =
                                                                    let uu____3627
                                                                    =
                                                                    let uu____3638
                                                                    =
                                                                    let uu____3647
                                                                    =
                                                                    let uu____3648
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3648 in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3647,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)") in
                                                                    let uu____3649
                                                                    =
                                                                    let uu____3660
                                                                    =
                                                                    let uu____3671
                                                                    =
                                                                    let uu____3680
                                                                    =
                                                                    let uu____3681
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3681 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3680,
                                                                    "Ignore the default module search paths") in
                                                                    let uu____3682
                                                                    =
                                                                    let uu____3693
                                                                    =
                                                                    let uu____3704
                                                                    =
                                                                    let uu____3713
                                                                    =
                                                                    let uu____3714
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3714 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3713,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)") in
                                                                    let uu____3715
                                                                    =
                                                                    let uu____3726
                                                                    =
                                                                    let uu____3737
                                                                    =
                                                                    let uu____3748
                                                                    =
                                                                    let uu____3757
                                                                    =
                                                                    let uu____3758
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3758 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3757,
                                                                    "Print the types of bound variables") in
                                                                    let uu____3759
                                                                    =
                                                                    let uu____3770
                                                                    =
                                                                    let uu____3779
                                                                    =
                                                                    let uu____3780
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3780 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3779,
                                                                    "Print inferred predicate transformers for all computation types") in
                                                                    let uu____3781
                                                                    =
                                                                    let uu____3792
                                                                    =
                                                                    let uu____3801
                                                                    =
                                                                    let uu____3802
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3802 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3801,
                                                                    "Print full names of variables") in
                                                                    let uu____3803
                                                                    =
                                                                    let uu____3814
                                                                    =
                                                                    let uu____3823
                                                                    =
                                                                    let uu____3824
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3824 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3823,
                                                                    "Print implicit arguments") in
                                                                    let uu____3825
                                                                    =
                                                                    let uu____3836
                                                                    =
                                                                    let uu____3845
                                                                    =
                                                                    let uu____3846
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3846 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3845,
                                                                    "Print universes") in
                                                                    let uu____3847
                                                                    =
                                                                    let uu____3858
                                                                    =
                                                                    let uu____3867
                                                                    =
                                                                    let uu____3868
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3868 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3867,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)") in
                                                                    let uu____3869
                                                                    =
                                                                    let uu____3880
                                                                    =
                                                                    let uu____3889
                                                                    =
                                                                    let uu____3890
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3890 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3889,
                                                                    "Print full names (deprecated; use --print_full_names instead)") in
                                                                    let uu____3891
                                                                    =
                                                                    let uu____3902
                                                                    =
                                                                    let uu____3911
                                                                    =
                                                                    let uu____3912
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3912 in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3911,
                                                                    "Print SMT query statistics") in
                                                                    let uu____3913
                                                                    =
                                                                    let uu____3924
                                                                    =
                                                                    let uu____3933
                                                                    =
                                                                    let uu____3934
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3934 in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3933,
                                                                    "Record a database of hints for efficient proof replay") in
                                                                    let uu____3935
                                                                    =
                                                                    let uu____3946
                                                                    =
                                                                    let uu____3957
                                                                    =
                                                                    let uu____3968
                                                                    =
                                                                    let uu____3977
                                                                    =
                                                                    let uu____3978
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3978 in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3977,
                                                                    " ") in
                                                                    let uu____3979
                                                                    =
                                                                    let uu____3990
                                                                    =
                                                                    let uu____4001
                                                                    =
                                                                    let uu____4012
                                                                    =
                                                                    let uu____4023
                                                                    =
                                                                    let uu____4034
                                                                    =
                                                                    let uu____4045
                                                                    =
                                                                    let uu____4054
                                                                    =
                                                                    let uu____4055
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4055 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4054,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)") in
                                                                    let uu____4056
                                                                    =
                                                                    let uu____4067
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
                                                                    "timing",
                                                                    uu____4087,
                                                                    "Print the time it takes to verify each top-level definition") in
                                                                    let uu____4089
                                                                    =
                                                                    let uu____4100
                                                                    =
                                                                    let uu____4109
                                                                    =
                                                                    let uu____4110
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4110 in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4109,
                                                                    "Don't print an error message; show an exception trace instead") in
                                                                    let uu____4111
                                                                    =
                                                                    let uu____4122
                                                                    =
                                                                    let uu____4131
                                                                    =
                                                                    let uu____4132
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4132 in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4131,
                                                                    "Emit output formatted for debugging") in
                                                                    let uu____4133
                                                                    =
                                                                    let uu____4144
                                                                    =
                                                                    let uu____4153
                                                                    =
                                                                    let uu____4154
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4154 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4153,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)") in
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
                                                                    "unsafe_tactic_exec",
                                                                    uu____4175,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.") in
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
                                                                    "use_eq_at_higher_order",
                                                                    uu____4197,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)") in
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
                                                                    "use_hints",
                                                                    uu____4219,
                                                                    "Use a previously recorded hints database for proof replay") in
                                                                    let uu____4221
                                                                    =
                                                                    let uu____4232
                                                                    =
                                                                    let uu____4241
                                                                    =
                                                                    let uu____4242
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4242 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4241,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database") in
                                                                    let uu____4243
                                                                    =
                                                                    let uu____4254
                                                                    =
                                                                    let uu____4265
                                                                    =
                                                                    let uu____4274
                                                                    =
                                                                    let uu____4275
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4275 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4274,
                                                                    "Do not run the tactic engine before discharging a VC") in
                                                                    let uu____4276
                                                                    =
                                                                    let uu____4287
                                                                    =
                                                                    let uu____4298
                                                                    =
                                                                    let uu____4307
                                                                    =
                                                                    let uu____4308
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4308 in
                                                                    (FStar_Getopt.noshort,
                                                                    "verify_all",
                                                                    uu____4307,
                                                                    "With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.") in
                                                                    let uu____4309
                                                                    =
                                                                    let uu____4320
                                                                    =
                                                                    let uu____4331
                                                                    =
                                                                    let uu____4342
                                                                    =
                                                                    let uu____4351
                                                                    =
                                                                    let uu____4352
                                                                    =
                                                                    let uu____4359
                                                                    =
                                                                    let uu____4360
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4360 in
                                                                    ((fun
                                                                    uu____4365
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____4359) in
                                                                    WithSideEffect
                                                                    uu____4352 in
                                                                    (118,
                                                                    "version",
                                                                    uu____4351,
                                                                    "Display version number") in
                                                                    let uu____4367
                                                                    =
                                                                    let uu____4378
                                                                    =
                                                                    let uu____4387
                                                                    =
                                                                    let uu____4388
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4388 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4387,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)") in
                                                                    let uu____4389
                                                                    =
                                                                    let uu____4400
                                                                    =
                                                                    let uu____4411
                                                                    =
                                                                    let uu____4420
                                                                    =
                                                                    let uu____4421
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4421 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4420,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness") in
                                                                    let uu____4422
                                                                    =
                                                                    let uu____4433
                                                                    =
                                                                    let uu____4444
                                                                    =
                                                                    let uu____4455
                                                                    =
                                                                    let uu____4466
                                                                    =
                                                                    let uu____4475
                                                                    =
                                                                    let uu____4476
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4476 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4475,
                                                                    "Don't check positivity of inductive types") in
                                                                    let uu____4477
                                                                    =
                                                                    let uu____4488
                                                                    =
                                                                    let uu____4497
                                                                    =
                                                                    let uu____4498
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4498 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4497,
                                                                    "Do not eta-expand coertions in generated OCaml") in
                                                                    let uu____4499
                                                                    =
                                                                    let uu____4510
                                                                    =
                                                                    let uu____4519
                                                                    =
                                                                    let uu____4520
                                                                    =
                                                                    let uu____4527
                                                                    =
                                                                    let uu____4528
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4528 in
                                                                    ((fun
                                                                    uu____4533
                                                                     ->
                                                                    (
                                                                    let uu____4535
                                                                    =
                                                                    specs () in
                                                                    display_usage_aux
                                                                    uu____4535);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____4527) in
                                                                    WithSideEffect
                                                                    uu____4520 in
                                                                    (104,
                                                                    "help",
                                                                    uu____4519,
                                                                    "Display this information") in
                                                                    [uu____4510] in
                                                                    uu____4488
                                                                    ::
                                                                    uu____4499 in
                                                                    uu____4466
                                                                    ::
                                                                    uu____4477 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4455 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4444 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4433 in
                                                                    uu____4411
                                                                    ::
                                                                    uu____4422 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4400 in
                                                                    uu____4378
                                                                    ::
                                                                    uu____4389 in
                                                                    uu____4342
                                                                    ::
                                                                    uu____4367 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4331 in
                                                                    (FStar_Getopt.noshort,
                                                                    "verify_module",
                                                                    (Accumulated
                                                                    (PostProcessed
                                                                    (pp_lowercase,
                                                                    (SimpleStr
                                                                    "module_name")))),
                                                                    "Name of the module to verify")
                                                                    ::
                                                                    uu____4320 in
                                                                    uu____4298
                                                                    ::
                                                                    uu____4309 in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (WithSideEffect
                                                                    ((fun
                                                                    uu____4674
                                                                     ->
                                                                    let uu____4675
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    set_option
                                                                    "z3refresh"
                                                                    uu____4675),
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "namespace | fact id")))),
                                                                    "Implies --z3refresh; prunes the context to include facts from the given namespace of fact id (multiple uses of this option will prune the context to include those facts that match any of the provided namespaces / fact ids")
                                                                    ::
                                                                    uu____4287 in
                                                                    uu____4265
                                                                    ::
                                                                    uu____4276 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4254 in
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
                                                                    uu____4144
                                                                    ::
                                                                    uu____4155 in
                                                                    uu____4122
                                                                    ::
                                                                    uu____4133 in
                                                                    uu____4100
                                                                    ::
                                                                    uu____4111 in
                                                                    uu____4078
                                                                    ::
                                                                    uu____4089 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4067 in
                                                                    uu____4045
                                                                    ::
                                                                    uu____4056 in
                                                                    (FStar_Getopt.noshort,
                                                                    "split_cases",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Partition VC of a match into groups of <positive_integer> cases")
                                                                    ::
                                                                    uu____4034 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4023 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4012 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4001 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3990 in
                                                                    uu____3968
                                                                    ::
                                                                    uu____3979 in
                                                                    (FStar_Getopt.noshort,
                                                                    "show_signatures",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Show the checked signatures for all top-level symbols in the module")
                                                                    ::
                                                                    uu____3957 in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3946 in
                                                                    uu____3924
                                                                    ::
                                                                    uu____3935 in
                                                                    uu____3902
                                                                    ::
                                                                    uu____3913 in
                                                                    uu____3880
                                                                    ::
                                                                    uu____3891 in
                                                                    uu____3858
                                                                    ::
                                                                    uu____3869 in
                                                                    uu____3836
                                                                    ::
                                                                    uu____3847 in
                                                                    uu____3814
                                                                    ::
                                                                    uu____3825 in
                                                                    uu____3792
                                                                    ::
                                                                    uu____3803 in
                                                                    uu____3770
                                                                    ::
                                                                    uu____3781 in
                                                                    uu____3748
                                                                    ::
                                                                    uu____3759 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3737 in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3726 in
                                                                    uu____3704
                                                                    ::
                                                                    uu____3715 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Do not extract code from this module")
                                                                    ::
                                                                    uu____3693 in
                                                                    uu____3671
                                                                    ::
                                                                    uu____3682 in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3660 in
                                                                    uu____3638
                                                                    ::
                                                                    uu____3649 in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3627 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3616 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3605 in
                                                                    uu____3583
                                                                    ::
                                                                    uu____3594 in
                                                                  uu____3561
                                                                    ::
                                                                    uu____3572 in
                                                                (FStar_Getopt.noshort,
                                                                  "load",
                                                                  (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                  "Load compiled module")
                                                                  ::
                                                                  uu____3550 in
                                                              uu____3528 ::
                                                                uu____3539 in
                                                            (FStar_Getopt.noshort,
                                                              "initial_ifuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                              :: uu____3517 in
                                                          (FStar_Getopt.noshort,
                                                            "initial_fuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of recursive functions to try initially (default 2)")
                                                            :: uu____3506 in
                                                        uu____3484 ::
                                                          uu____3495 in
                                                      (FStar_Getopt.noshort,
                                                        "include",
                                                        (ReverseAccumulated
                                                           (PathStr "path")),
                                                        "A directory in which to search for files included on the command line")
                                                        :: uu____3473 in
                                                    uu____3451 :: uu____3462 in
                                                  uu____3429 :: uu____3440 in
                                                uu____3407 :: uu____3418 in
                                              (FStar_Getopt.noshort,
                                                "hint_file",
                                                (PathStr "path"),
                                                "Read/write hints to <path> (instead of module-specific hints files)")
                                                :: uu____3396 in
                                            uu____3374 :: uu____3385 in
                                          uu____3352 :: uu____3363 in
                                        (FStar_Getopt.noshort,
                                          "gen_native_tactics",
                                          (PathStr "[path]"),
                                          "Compile all user tactics used in the module in <path>")
                                          :: uu____3341 in
                                      (FStar_Getopt.noshort, "fstar_home",
                                        (PathStr "dir"),
                                        "Set the FSTAR_HOME variable to <dir>")
                                        :: uu____3330 in
                                    (FStar_Getopt.noshort,
                                      "extract_namespace",
                                      (Accumulated
                                         (PostProcessed
                                            (pp_lowercase,
                                              (SimpleStr "namespace name")))),
                                      "Only extract modules in the specified namespace")
                                      :: uu____3319 in
                                  (FStar_Getopt.noshort, "extract_module",
                                    (Accumulated
                                       (PostProcessed
                                          (pp_lowercase,
                                            (SimpleStr "module_name")))),
                                    "Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                    :: uu____3308 in
                                uu____3286 :: uu____3297 in
                              uu____3264 :: uu____3275 in
                            uu____3242 :: uu____3253 in
                          (FStar_Getopt.noshort, "dump_module",
                            (Accumulated (SimpleStr "module_name")), "") ::
                            uu____3231 in
                        uu____3209 :: uu____3220 in
                      uu____3187 :: uu____3198 in
                    uu____3165 :: uu____3176 in
                  (FStar_Getopt.noshort, "dep", (EnumStr ["make"; "graph"]),
                    "Output the transitive closure of the dependency graph in a format suitable for the given tool")
                    :: uu____3154 in
                (FStar_Getopt.noshort, "debug_level",
                  (Accumulated
                     (OpenEnumStr
                        (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                  "Control the verbosity of debugging info") :: uu____3143 in
              (FStar_Getopt.noshort, "debug",
                (Accumulated (SimpleStr "module_name")),
                "Print lots of debugging information while checking module")
                :: uu____3132 in
            (FStar_Getopt.noshort, "codegen-lib",
              (Accumulated (SimpleStr "namespace")),
              "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
              :: uu____3121 in
          (FStar_Getopt.noshort, "codegen",
            (EnumStr ["OCaml"; "FSharp"; "Kremlin"]),
            "Generate code for execution") :: uu____3110 in
        uu____3088 :: uu____3099 in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____3077 in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____3066
and specs: Prims.unit -> FStar_Getopt.opt Prims.list =
  fun uu____5260  ->
    let uu____5263 = specs_with_types () in
    FStar_List.map
      (fun uu____5288  ->
         match uu____5288 with
         | (short,long,typ,doc) ->
             let uu____5301 =
               let uu____5312 = arg_spec_of_opt_type long typ in
               (short, long, uu____5312, doc) in
             mk_spec uu____5301) uu____5263
let settable: Prims.string -> Prims.bool =
  fun uu___54_5326  ->
    match uu___54_5326 with
    | "admit_smt_queries" -> true
    | "admit_except" -> true
    | "debug" -> true
    | "debug_level" -> true
    | "detail_errors" -> true
    | "detail_hint_replay" -> true
    | "eager_inference" -> true
    | "hide_genident_nums" -> true
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
    | "show_signatures" -> true
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
    | "using_facts_from" -> true
    | "__temp_no_proj" -> true
    | "reuse_hint_for" -> true
    | "z3rlimit_factor" -> true
    | "z3rlimit" -> true
    | "z3refresh" -> true
    | uu____5327 -> false
let resettable: Prims.string -> Prims.bool =
  fun s  -> ((settable s) || (s = "z3seed")) || (s = "z3cliopt")
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
       (fun uu____5385  ->
          match uu____5385 with
          | (uu____5396,x,uu____5398,uu____5399) -> settable x))
let resettable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5445  ->
          match uu____5445 with
          | (uu____5456,x,uu____5458,uu____5459) -> resettable x))
let display_usage: Prims.unit -> Prims.unit =
  fun uu____5467  ->
    let uu____5468 = specs () in display_usage_aux uu____5468
let fstar_home: Prims.unit -> Prims.string =
  fun uu____5484  ->
    let uu____5485 = get_fstar_home () in
    match uu____5485 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        ((let uu____5491 =
            let uu____5496 = mk_string x1 in ("fstar_home", uu____5496) in
          set_option' uu____5491);
         x1)
    | FStar_Pervasives_Native.Some x -> x
exception File_argument of Prims.string
let uu___is_File_argument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____5505 -> true
    | uu____5506 -> false
let __proj__File_argument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____5514 -> uu____5514
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
          let uu____5560 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____5560
let file_list_: Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let parse_cmd_line:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____5583  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5588 =
             let uu____5591 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____5591 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____5588) in
    let uu____5694 =
      let uu____5697 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5697 in
    (res, uu____5694)
let file_list: Prims.unit -> Prims.string Prims.list =
  fun uu____5757  -> FStar_ST.op_Bang file_list_
let restore_cmd_line_options: Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____5818 = specs () in
       FStar_Getopt.parse_cmdline uu____5818 (fun x  -> ()) in
     (let uu____5824 =
        let uu____5829 =
          let uu____5830 = FStar_List.map mk_string old_verify_module in
          List uu____5830 in
        ("verify_module", uu____5829) in
      set_option' uu____5824);
     r)
let module_name_of_file_name: Prims.string -> Prims.string =
  fun f  ->
    let f1 = FStar_Util.basename f in
    let f2 =
      let uu____5839 =
        let uu____5840 =
          let uu____5841 =
            let uu____5842 = FStar_Util.get_file_extension f1 in
            FStar_String.length uu____5842 in
          (FStar_String.length f1) - uu____5841 in
        uu____5840 - (Prims.parse_int "1") in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5839 in
    FStar_String.lowercase f2
let should_verify: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5847 = get_lax () in
    if uu____5847
    then false
    else
      (let uu____5849 = get_verify_all () in
       if uu____5849
       then true
       else
         (let uu____5851 = get_verify_module () in
          match uu____5851 with
          | [] ->
              let uu____5854 = file_list () in
              FStar_List.existsML
                (fun f  ->
                   let uu____5860 = module_name_of_file_name f in
                   uu____5860 = m) uu____5854
          | l -> FStar_List.contains (FStar_String.lowercase m) l))
let should_verify_file: Prims.string -> Prims.bool =
  fun fn  ->
    let uu____5868 = module_name_of_file_name fn in should_verify uu____5868
let dont_gen_projectors: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5873 = get___temp_no_proj () in
    FStar_List.contains m uu____5873
let should_print_message: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5880 = should_verify m in
    if uu____5880 then m <> "Prims" else false
let include_path: Prims.unit -> Prims.string Prims.list =
  fun uu____5887  ->
    let uu____5888 = get_no_default_includes () in
    if uu____5888
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____5896 =
         let uu____5899 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____5899
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____5912 =
         let uu____5915 = get_include () in
         FStar_List.append uu____5915 ["."] in
       FStar_List.append uu____5896 uu____5912)
let find_file: Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____5924 = FStar_Util.is_path_absolute filename in
    if uu____5924
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5931 =
         let uu____5934 = include_path () in FStar_List.rev uu____5934 in
       FStar_Util.find_map uu____5931
         (fun p  ->
            let path = FStar_Util.join_paths p filename in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
let prims: Prims.unit -> Prims.string =
  fun uu____5947  ->
    let uu____5948 = get_prims () in
    match uu____5948 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst" in
        let uu____5952 = find_file filename in
        (match uu____5952 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5956 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename in
             failwith uu____5956)
    | FStar_Pervasives_Native.Some x -> x
let prims_basename: Prims.unit -> Prims.string =
  fun uu____5961  ->
    let uu____5962 = prims () in FStar_Util.basename uu____5962
let pervasives: Prims.unit -> Prims.string =
  fun uu____5966  ->
    let filename = "FStar.Pervasives.fst" in
    let uu____5968 = find_file filename in
    match uu____5968 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5972 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5972
let pervasives_basename: Prims.unit -> Prims.string =
  fun uu____5976  ->
    let uu____5977 = pervasives () in FStar_Util.basename uu____5977
let pervasives_native_basename: Prims.unit -> Prims.string =
  fun uu____5981  ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____5983 = find_file filename in
    match uu____5983 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5987 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5987
let prepend_output_dir: Prims.string -> Prims.string =
  fun fname  ->
    let uu____5992 = get_odir () in
    match uu____5992 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
let __temp_no_proj: Prims.string -> Prims.bool =
  fun s  ->
    let uu____6000 = get___temp_no_proj () in
    FStar_All.pipe_right uu____6000 (FStar_List.contains s)
let admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____6008  -> get_admit_smt_queries ()
let admit_except: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____6014  -> get_admit_except ()
let cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____6018  -> get_cache_checked_modules ()
let codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____6024  -> get_codegen ()
let codegen_libs: Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____6032  ->
    let uu____6033 = get_codegen_lib () in
    FStar_All.pipe_right uu____6033
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
let debug_any: Prims.unit -> Prims.bool =
  fun uu____6049  -> let uu____6050 = get_debug () in uu____6050 <> []
let debug_at_level: Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      (let uu____6065 = get_debug () in
       FStar_All.pipe_right uu____6065 (FStar_List.contains modul)) &&
        (debug_level_geq level)
let dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____6075  -> get_dep ()
let detail_errors: Prims.unit -> Prims.bool =
  fun uu____6079  -> get_detail_errors ()
let detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____6083  -> get_detail_hint_replay ()
let doc: Prims.unit -> Prims.bool = fun uu____6087  -> get_doc ()
let dump_module: Prims.string -> Prims.bool =
  fun s  ->
    let uu____6092 = get_dump_module () in
    FStar_All.pipe_right uu____6092 (FStar_List.contains s)
let eager_inference: Prims.unit -> Prims.bool =
  fun uu____6100  -> get_eager_inference ()
let explicit_deps: Prims.unit -> Prims.bool =
  fun uu____6104  -> get_explicit_deps ()
let extract_all: Prims.unit -> Prims.bool =
  fun uu____6108  -> get_extract_all ()
let fs_typ_app: Prims.string -> Prims.bool =
  fun filename  ->
    let uu____6113 = FStar_ST.op_Bang light_off_files in
    FStar_List.contains filename uu____6113
let gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____6171  -> get_gen_native_tactics ()
let full_context_dependency: Prims.unit -> Prims.bool =
  fun uu____6175  -> true
let hide_genident_nums: Prims.unit -> Prims.bool =
  fun uu____6179  -> get_hide_genident_nums ()
let hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____6183  -> get_hide_uvar_nums ()
let hint_info: Prims.unit -> Prims.bool =
  fun uu____6187  -> (get_hint_info ()) || (get_query_stats ())
let hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____6193  -> get_hint_file ()
let ide: Prims.unit -> Prims.bool = fun uu____6197  -> get_ide ()
let indent: Prims.unit -> Prims.bool = fun uu____6201  -> get_indent ()
let initial_fuel: Prims.unit -> Prims.int =
  fun uu____6205  ->
    let uu____6206 = get_initial_fuel () in
    let uu____6207 = get_max_fuel () in Prims.min uu____6206 uu____6207
let initial_ifuel: Prims.unit -> Prims.int =
  fun uu____6211  ->
    let uu____6212 = get_initial_ifuel () in
    let uu____6213 = get_max_ifuel () in Prims.min uu____6212 uu____6213
let interactive: Prims.unit -> Prims.bool =
  fun uu____6217  -> (get_in ()) || (get_ide ())
let lax: Prims.unit -> Prims.bool = fun uu____6221  -> get_lax ()
let load: Prims.unit -> Prims.string Prims.list =
  fun uu____6227  -> get_load ()
let legacy_interactive: Prims.unit -> Prims.bool =
  fun uu____6231  -> get_in ()
let log_queries: Prims.unit -> Prims.bool =
  fun uu____6235  -> get_log_queries ()
let log_types: Prims.unit -> Prims.bool = fun uu____6239  -> get_log_types ()
let max_fuel: Prims.unit -> Prims.int = fun uu____6243  -> get_max_fuel ()
let max_ifuel: Prims.unit -> Prims.int = fun uu____6247  -> get_max_ifuel ()
let min_fuel: Prims.unit -> Prims.int = fun uu____6251  -> get_min_fuel ()
let ml_ish: Prims.unit -> Prims.bool = fun uu____6255  -> get_MLish ()
let set_ml_ish: Prims.unit -> Prims.unit =
  fun uu____6259  -> set_option "MLish" (Bool true)
let n_cores: Prims.unit -> Prims.int = fun uu____6263  -> get_n_cores ()
let no_default_includes: Prims.unit -> Prims.bool =
  fun uu____6267  -> get_no_default_includes ()
let no_extract: Prims.string -> Prims.bool =
  fun s  ->
    let uu____6272 = get_no_extract () in
    FStar_All.pipe_right uu____6272 (FStar_List.contains s)
let no_location_info: Prims.unit -> Prims.bool =
  fun uu____6280  -> get_no_location_info ()
let output_dir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____6286  -> get_odir ()
let ugly: Prims.unit -> Prims.bool = fun uu____6290  -> get_ugly ()
let print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____6294  -> get_print_bound_var_types ()
let print_effect_args: Prims.unit -> Prims.bool =
  fun uu____6298  -> get_print_effect_args ()
let print_implicits: Prims.unit -> Prims.bool =
  fun uu____6302  -> get_print_implicits ()
let print_real_names: Prims.unit -> Prims.bool =
  fun uu____6306  -> (get_prn ()) || (get_print_full_names ())
let print_universes: Prims.unit -> Prims.bool =
  fun uu____6310  -> get_print_universes ()
let print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____6314  -> (get_print_z3_statistics ()) || (get_query_stats ())
let query_stats: Prims.unit -> Prims.bool =
  fun uu____6318  -> get_query_stats ()
let record_hints: Prims.unit -> Prims.bool =
  fun uu____6322  -> get_record_hints ()
let reuse_hint_for: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____6328  -> get_reuse_hint_for ()
let silent: Prims.unit -> Prims.bool = fun uu____6332  -> get_silent ()
let smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____6336  -> get_smtencoding_elim_box ()
let smtencoding_nl_arith_native: Prims.unit -> Prims.bool =
  fun uu____6340  ->
    let uu____6341 = get_smtencoding_nl_arith_repr () in
    uu____6341 = "native"
let smtencoding_nl_arith_wrapped: Prims.unit -> Prims.bool =
  fun uu____6345  ->
    let uu____6346 = get_smtencoding_nl_arith_repr () in
    uu____6346 = "wrapped"
let smtencoding_nl_arith_default: Prims.unit -> Prims.bool =
  fun uu____6350  ->
    let uu____6351 = get_smtencoding_nl_arith_repr () in
    uu____6351 = "boxwrap"
let smtencoding_l_arith_native: Prims.unit -> Prims.bool =
  fun uu____6355  ->
    let uu____6356 = get_smtencoding_l_arith_repr () in uu____6356 = "native"
let smtencoding_l_arith_default: Prims.unit -> Prims.bool =
  fun uu____6360  ->
    let uu____6361 = get_smtencoding_l_arith_repr () in
    uu____6361 = "boxwrap"
let split_cases: Prims.unit -> Prims.int =
  fun uu____6365  -> get_split_cases ()
let tactic_trace: Prims.unit -> Prims.bool =
  fun uu____6369  -> get_tactic_trace ()
let tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____6373  -> get_tactic_trace_d ()
let timing: Prims.unit -> Prims.bool = fun uu____6377  -> get_timing ()
let trace_error: Prims.unit -> Prims.bool =
  fun uu____6381  -> get_trace_error ()
let unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____6385  -> get_unthrottle_inductives ()
let unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____6389  -> get_unsafe_tactic_exec ()
let use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____6393  -> get_use_eq_at_higher_order ()
let use_hints: Prims.unit -> Prims.bool = fun uu____6397  -> get_use_hints ()
let use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____6401  -> get_use_hint_hashes ()
let use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____6407  -> get_use_native_tactics ()
let use_tactics: Prims.unit -> Prims.bool =
  fun uu____6411  -> get_use_tactics ()
let using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____6419  -> get_using_facts_from ()
let verify_all: Prims.unit -> Prims.bool =
  fun uu____6423  -> get_verify_all ()
let verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____6429  -> get_verify_module ()
let warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____6433  -> get_warn_default_effects ()
let z3_exe: Prims.unit -> Prims.string =
  fun uu____6437  ->
    let uu____6438 = get_smt () in
    match uu____6438 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let z3_cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____6447  -> get_z3cliopt ()
let z3_refresh: Prims.unit -> Prims.bool =
  fun uu____6451  -> get_z3refresh ()
let z3_rlimit: Prims.unit -> Prims.int = fun uu____6455  -> get_z3rlimit ()
let z3_rlimit_factor: Prims.unit -> Prims.int =
  fun uu____6459  -> get_z3rlimit_factor ()
let z3_seed: Prims.unit -> Prims.int = fun uu____6463  -> get_z3seed ()
let no_positivity: Prims.unit -> Prims.bool =
  fun uu____6467  -> get_no_positivity ()
let ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____6471  -> get_ml_no_eta_expand_coertions ()
let should_extract: Prims.string -> Prims.bool =
  fun m  ->
    (let uu____6478 = no_extract m in Prims.op_Negation uu____6478) &&
      ((extract_all ()) ||
         (let uu____6481 = get_extract_module () in
          match uu____6481 with
          | [] ->
              let uu____6484 = get_extract_namespace () in
              (match uu____6484 with
               | [] -> true
               | ns ->
                   FStar_Util.for_some
                     (FStar_Util.starts_with (FStar_String.lowercase m)) ns)
          | l -> FStar_List.contains (FStar_String.lowercase m) l))