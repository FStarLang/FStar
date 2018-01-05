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
  fun uu____1009  ->
    let o = peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let clear: Prims.unit -> Prims.unit =
  fun uu____1024  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50") in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
let _run: Prims.unit = clear ()
let get_option: Prims.string -> option_val =
  fun s  ->
    let uu____1083 =
      let uu____1086 = peek () in FStar_Util.smap_try_find uu____1086 s in
    match uu____1083 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
let lookup_opt:
  'Auu____1093 . Prims.string -> (option_val -> 'Auu____1093) -> 'Auu____1093
  = fun s  -> fun c  -> c (get_option s)
let get_admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____1109  -> lookup_opt "admit_smt_queries" as_bool
let get_admit_except:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1114  -> lookup_opt "admit_except" (as_option as_string)
let get_cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____1119  -> lookup_opt "cache_checked_modules" as_bool
let get_codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1124  -> lookup_opt "codegen" (as_option as_string)
let get_codegen_lib: Prims.unit -> Prims.string Prims.list =
  fun uu____1131  -> lookup_opt "codegen-lib" (as_list as_string)
let get_debug: Prims.unit -> Prims.string Prims.list =
  fun uu____1138  -> lookup_opt "debug" (as_list as_string)
let get_debug_level: Prims.unit -> Prims.string Prims.list =
  fun uu____1145  -> lookup_opt "debug_level" (as_list as_string)
let get_dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1152  -> lookup_opt "dep" (as_option as_string)
let get_detail_errors: Prims.unit -> Prims.bool =
  fun uu____1157  -> lookup_opt "detail_errors" as_bool
let get_detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____1160  -> lookup_opt "detail_hint_replay" as_bool
let get_doc: Prims.unit -> Prims.bool =
  fun uu____1163  -> lookup_opt "doc" as_bool
let get_dump_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1168  -> lookup_opt "dump_module" (as_list as_string)
let get_eager_inference: Prims.unit -> Prims.bool =
  fun uu____1173  -> lookup_opt "eager_inference" as_bool
let get_expose_interfaces: Prims.unit -> Prims.bool =
  fun uu____1176  -> lookup_opt "expose_interfaces" as_bool
let get_extract: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1181  -> lookup_opt "extract" (as_option as_string)
let get_extract_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1188  -> lookup_opt "extract_module" (as_list as_string)
let get_extract_namespace: Prims.unit -> Prims.string Prims.list =
  fun uu____1195  -> lookup_opt "extract_namespace" (as_list as_string)
let get_fs_typ_app: Prims.unit -> Prims.bool =
  fun uu____1200  -> lookup_opt "fs_typ_app" as_bool
let get_fstar_home: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1205  -> lookup_opt "fstar_home" (as_option as_string)
let get_gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1212  -> lookup_opt "gen_native_tactics" (as_option as_string)
let get_hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____1217  -> lookup_opt "hide_uvar_nums" as_bool
let get_hint_info: Prims.unit -> Prims.bool =
  fun uu____1220  -> lookup_opt "hint_info" as_bool
let get_hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1225  -> lookup_opt "hint_file" (as_option as_string)
let get_in: Prims.unit -> Prims.bool =
  fun uu____1230  -> lookup_opt "in" as_bool
let get_ide: Prims.unit -> Prims.bool =
  fun uu____1233  -> lookup_opt "ide" as_bool
let get_include: Prims.unit -> Prims.string Prims.list =
  fun uu____1238  -> lookup_opt "include" (as_list as_string)
let get_indent: Prims.unit -> Prims.bool =
  fun uu____1243  -> lookup_opt "indent" as_bool
let get_initial_fuel: Prims.unit -> Prims.int =
  fun uu____1246  -> lookup_opt "initial_fuel" as_int
let get_initial_ifuel: Prims.unit -> Prims.int =
  fun uu____1249  -> lookup_opt "initial_ifuel" as_int
let get_lax: Prims.unit -> Prims.bool =
  fun uu____1252  -> lookup_opt "lax" as_bool
let get_load: Prims.unit -> Prims.string Prims.list =
  fun uu____1257  -> lookup_opt "load" (as_list as_string)
let get_log_queries: Prims.unit -> Prims.bool =
  fun uu____1262  -> lookup_opt "log_queries" as_bool
let get_log_types: Prims.unit -> Prims.bool =
  fun uu____1265  -> lookup_opt "log_types" as_bool
let get_max_fuel: Prims.unit -> Prims.int =
  fun uu____1268  -> lookup_opt "max_fuel" as_int
let get_max_ifuel: Prims.unit -> Prims.int =
  fun uu____1271  -> lookup_opt "max_ifuel" as_int
let get_min_fuel: Prims.unit -> Prims.int =
  fun uu____1274  -> lookup_opt "min_fuel" as_int
let get_MLish: Prims.unit -> Prims.bool =
  fun uu____1277  -> lookup_opt "MLish" as_bool
let get_n_cores: Prims.unit -> Prims.int =
  fun uu____1280  -> lookup_opt "n_cores" as_int
let get_no_default_includes: Prims.unit -> Prims.bool =
  fun uu____1283  -> lookup_opt "no_default_includes" as_bool
let get_no_extract: Prims.unit -> Prims.string Prims.list =
  fun uu____1288  -> lookup_opt "no_extract" (as_list as_string)
let get_no_location_info: Prims.unit -> Prims.bool =
  fun uu____1293  -> lookup_opt "no_location_info" as_bool
let get_odir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1298  -> lookup_opt "odir" (as_option as_string)
let get_ugly: Prims.unit -> Prims.bool =
  fun uu____1303  -> lookup_opt "ugly" as_bool
let get_prims: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1308  -> lookup_opt "prims" (as_option as_string)
let get_print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____1313  -> lookup_opt "print_bound_var_types" as_bool
let get_print_effect_args: Prims.unit -> Prims.bool =
  fun uu____1316  -> lookup_opt "print_effect_args" as_bool
let get_print_full_names: Prims.unit -> Prims.bool =
  fun uu____1319  -> lookup_opt "print_full_names" as_bool
let get_print_implicits: Prims.unit -> Prims.bool =
  fun uu____1322  -> lookup_opt "print_implicits" as_bool
let get_print_universes: Prims.unit -> Prims.bool =
  fun uu____1325  -> lookup_opt "print_universes" as_bool
let get_print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____1328  -> lookup_opt "print_z3_statistics" as_bool
let get_prn: Prims.unit -> Prims.bool =
  fun uu____1331  -> lookup_opt "prn" as_bool
let get_query_stats: Prims.unit -> Prims.bool =
  fun uu____1334  -> lookup_opt "query_stats" as_bool
let get_record_hints: Prims.unit -> Prims.bool =
  fun uu____1337  -> lookup_opt "record_hints" as_bool
let get_reuse_hint_for:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1342  -> lookup_opt "reuse_hint_for" (as_option as_string)
let get_silent: Prims.unit -> Prims.bool =
  fun uu____1347  -> lookup_opt "silent" as_bool
let get_smt: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1352  -> lookup_opt "smt" (as_option as_string)
let get_smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____1357  -> lookup_opt "smtencoding.elim_box" as_bool
let get_smtencoding_nl_arith_repr: Prims.unit -> Prims.string =
  fun uu____1360  -> lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr: Prims.unit -> Prims.string =
  fun uu____1363  -> lookup_opt "smtencoding.l_arith_repr" as_string
let get_tactic_raw_binders: Prims.unit -> Prims.bool =
  fun uu____1366  -> lookup_opt "tactic_raw_binders" as_bool
let get_tactic_trace: Prims.unit -> Prims.bool =
  fun uu____1369  -> lookup_opt "tactic_trace" as_bool
let get_tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____1372  -> lookup_opt "tactic_trace_d" as_int
let get_timing: Prims.unit -> Prims.bool =
  fun uu____1375  -> lookup_opt "timing" as_bool
let get_trace_error: Prims.unit -> Prims.bool =
  fun uu____1378  -> lookup_opt "trace_error" as_bool
let get_unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____1381  -> lookup_opt "unthrottle_inductives" as_bool
let get_unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____1384  -> lookup_opt "unsafe_tactic_exec" as_bool
let get_use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____1387  -> lookup_opt "use_eq_at_higher_order" as_bool
let get_use_hints: Prims.unit -> Prims.bool =
  fun uu____1390  -> lookup_opt "use_hints" as_bool
let get_use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____1393  -> lookup_opt "use_hint_hashes" as_bool
let get_use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1398  -> lookup_opt "use_native_tactics" (as_option as_string)
let get_use_tactics: Prims.unit -> Prims.bool =
  fun uu____1403  ->
    let uu____1404 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____1404
let get_using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1411  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let get_vcgen_optimize_bind_as_seq:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1422  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
let get_verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1429  -> lookup_opt "verify_module" (as_list as_string)
let get___temp_no_proj: Prims.unit -> Prims.string Prims.list =
  fun uu____1436  -> lookup_opt "__temp_no_proj" (as_list as_string)
let get_version: Prims.unit -> Prims.bool =
  fun uu____1441  -> lookup_opt "version" as_bool
let get_warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____1444  -> lookup_opt "warn_default_effects" as_bool
let get_z3cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____1449  -> lookup_opt "z3cliopt" (as_list as_string)
let get_z3refresh: Prims.unit -> Prims.bool =
  fun uu____1454  -> lookup_opt "z3refresh" as_bool
let get_z3rlimit: Prims.unit -> Prims.int =
  fun uu____1457  -> lookup_opt "z3rlimit" as_int
let get_z3rlimit_factor: Prims.unit -> Prims.int =
  fun uu____1460  -> lookup_opt "z3rlimit_factor" as_int
let get_z3seed: Prims.unit -> Prims.int =
  fun uu____1463  -> lookup_opt "z3seed" as_int
let get_use_two_phase_tc: Prims.unit -> Prims.bool =
  fun uu____1466  -> lookup_opt "use_two_phase_tc" as_bool
let get_no_positivity: Prims.unit -> Prims.bool =
  fun uu____1469  -> lookup_opt "__no_positivity" as_bool
let get_ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____1472  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool
let get_warn_error: Prims.unit -> Prims.string =
  fun uu____1475  -> lookup_opt "warn_error" as_string
let dlevel: Prims.string -> debug_level_t =
  fun uu___39_1478  ->
    match uu___39_1478 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let one_debug_level_geq: debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1486 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let debug_level_geq: debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____1490 = get_debug_level () in
    FStar_All.pipe_right uu____1490
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
let universe_include_path_base_dirs: Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"]
let _version: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _platform: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _compiler: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _date: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _commit: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let display_version: Prims.unit -> Prims.unit =
  fun uu____1621  ->
    let uu____1622 =
      let uu____1623 = FStar_ST.op_Bang _version in
      let uu____1643 = FStar_ST.op_Bang _platform in
      let uu____1663 = FStar_ST.op_Bang _compiler in
      let uu____1683 = FStar_ST.op_Bang _date in
      let uu____1703 = FStar_ST.op_Bang _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1623
        uu____1643 uu____1663 uu____1683 uu____1703 in
    FStar_Util.print_string uu____1622
let display_usage_aux:
  'Auu____1726 'Auu____1727 .
    ('Auu____1727,Prims.string,'Auu____1726 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____1774  ->
         match uu____1774 with
         | (uu____1785,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____1796 =
                      let uu____1797 = FStar_Util.colorize_bold flag in
                      FStar_Util.format1 "  --%s\n" uu____1797 in
                    FStar_Util.print_string uu____1796
                  else
                    (let uu____1799 =
                       let uu____1800 = FStar_Util.colorize_bold flag in
                       FStar_Util.format2 "  --%s  %s\n" uu____1800 doc in
                     FStar_Util.print_string uu____1799)
              | FStar_Getopt.OneArg (uu____1801,argname) ->
                  if doc = ""
                  then
                    let uu____1807 =
                      let uu____1808 = FStar_Util.colorize_bold flag in
                      let uu____1809 = FStar_Util.colorize_bold argname in
                      FStar_Util.format2 "  --%s %s\n" uu____1808 uu____1809 in
                    FStar_Util.print_string uu____1807
                  else
                    (let uu____1811 =
                       let uu____1812 = FStar_Util.colorize_bold flag in
                       let uu____1813 = FStar_Util.colorize_bold argname in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____1812
                         uu____1813 doc in
                     FStar_Util.print_string uu____1811))) specs
let mk_spec:
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____1837 = o in
    match uu____1837 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____1867 =
                let uu____1868 = f () in set_option name uu____1868 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____1879 = f x in set_option name uu____1879 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____1893 = lookup_opt name (as_option as_list') in
        FStar_Util.dflt [] uu____1893 in
      mk_list (value :: prev_values)
let reverse_accumulated_option: Prims.string -> option_val -> option_val =
  fun name  ->
    fun value  ->
      let uu____1912 =
        let uu____1915 = lookup_opt name as_list' in
        FStar_List.append uu____1915 [value] in
      mk_list uu____1912
let accumulate_string:
  'Auu____1924 .
    Prims.string ->
      ('Auu____1924 -> Prims.string) -> 'Auu____1924 -> Prims.unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____1942 =
          let uu____1943 =
            let uu____1944 = post_processor value in mk_string uu____1944 in
          accumulated_option name uu____1943 in
        set_option name uu____1942
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
    match projectee with | Const _0 -> true | uu____2022 -> false
let __proj__Const__item___0: opt_type -> option_val =
  fun projectee  -> match projectee with | Const _0 -> _0
let uu___is_IntStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2034 -> false
let __proj__IntStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | IntStr _0 -> _0
let uu___is_BoolStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2045 -> false
let uu___is_PathStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2050 -> false
let __proj__PathStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | PathStr _0 -> _0
let uu___is_SimpleStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2062 -> false
let __proj__SimpleStr__item___0: opt_type -> Prims.string =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0
let uu___is_EnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2076 -> false
let __proj__EnumStr__item___0: opt_type -> Prims.string Prims.list =
  fun projectee  -> match projectee with | EnumStr _0 -> _0
let uu___is_OpenEnumStr: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2100 -> false
let __proj__OpenEnumStr__item___0:
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0
let uu___is_PostProcessed: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2136 -> false
let __proj__PostProcessed__item___0:
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0
let uu___is_Accumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2166 -> false
let __proj__Accumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | Accumulated _0 -> _0
let uu___is_ReverseAccumulated: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2178 -> false
let __proj__ReverseAccumulated__item___0: opt_type -> opt_type =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0
let uu___is_WithSideEffect: opt_type -> Prims.bool =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2196 -> false
let __proj__WithSideEffect__item___0:
  opt_type ->
    (Prims.unit -> Prims.unit,opt_type) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | WithSideEffect _0 -> _0
exception InvalidArgument of Prims.string
let uu___is_InvalidArgument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2228 -> true
    | uu____2229 -> false
let __proj__InvalidArgument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2236 -> uu____2236
let rec parse_opt_val: Prims.string -> opt_type -> Prims.string -> option_val
  =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2250 ->
              let uu____2251 = FStar_Util.safe_int_of_string str_val in
              (match uu____2251 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2255 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name) in
              mk_bool uu____2255
          | PathStr uu____2258 -> mk_path str_val
          | SimpleStr uu____2259 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2264 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2277 = parse_opt_val opt_name elem_spec str_val in
              pp uu____2277
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
            let uu____2294 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1 in
            failwith uu____2294
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
    | PostProcessed (uu____2327,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2335,elem_spec) -> desc_of_opt_type elem_spec
let rec arg_spec_of_opt_type:
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ in
      let uu____2354 = desc_of_opt_type typ in
      match uu____2354 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2360  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
let pp_validate_dir: option_val -> option_val =
  fun p  -> let pp = as_string p in FStar_Util.mkdir false pp; p
let pp_lowercase: option_val -> option_val =
  fun s  ->
    let uu____2372 =
      let uu____2373 = as_string s in FStar_String.lowercase uu____2373 in
    mk_string uu____2372
let rec specs_with_types:
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun uu____2390  ->
    let uu____2401 =
      let uu____2412 =
        let uu____2423 =
          let uu____2432 = let uu____2433 = mk_bool true in Const uu____2433 in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2432,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying") in
        let uu____2434 =
          let uu____2445 =
            let uu____2456 =
              let uu____2467 =
                let uu____2478 =
                  let uu____2489 =
                    let uu____2500 =
                      let uu____2509 =
                        let uu____2510 = mk_bool true in Const uu____2510 in
                      (FStar_Getopt.noshort, "detail_errors", uu____2509,
                        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1") in
                    let uu____2511 =
                      let uu____2522 =
                        let uu____2531 =
                          let uu____2532 = mk_bool true in Const uu____2532 in
                        (FStar_Getopt.noshort, "detail_hint_replay",
                          uu____2531,
                          "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1") in
                      let uu____2533 =
                        let uu____2544 =
                          let uu____2553 =
                            let uu____2554 = mk_bool true in Const uu____2554 in
                          (FStar_Getopt.noshort, "doc", uu____2553,
                            "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.") in
                        let uu____2555 =
                          let uu____2566 =
                            let uu____2577 =
                              let uu____2586 =
                                let uu____2587 = mk_bool true in
                                Const uu____2587 in
                              (FStar_Getopt.noshort, "eager_inference",
                                uu____2586,
                                "Solve all type-inference constraints eagerly; more efficient but at the cost of generality") in
                            let uu____2588 =
                              let uu____2599 =
                                let uu____2610 =
                                  let uu____2621 =
                                    let uu____2632 =
                                      let uu____2641 =
                                        let uu____2642 = mk_bool true in
                                        Const uu____2642 in
                                      (FStar_Getopt.noshort,
                                        "expose_interfaces", uu____2641,
                                        "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)") in
                                    let uu____2643 =
                                      let uu____2654 =
                                        let uu____2665 =
                                          let uu____2676 =
                                            let uu____2685 =
                                              let uu____2686 = mk_bool true in
                                              Const uu____2686 in
                                            (FStar_Getopt.noshort,
                                              "hide_uvar_nums", uu____2685,
                                              "Don't print unification variable numbers") in
                                          let uu____2687 =
                                            let uu____2698 =
                                              let uu____2709 =
                                                let uu____2718 =
                                                  let uu____2719 =
                                                    mk_bool true in
                                                  Const uu____2719 in
                                                (FStar_Getopt.noshort,
                                                  "hint_info", uu____2718,
                                                  "Print information regarding hints (deprecated; use --query_stats instead)") in
                                              let uu____2720 =
                                                let uu____2731 =
                                                  let uu____2740 =
                                                    let uu____2741 =
                                                      mk_bool true in
                                                    Const uu____2741 in
                                                  (FStar_Getopt.noshort,
                                                    "in", uu____2740,
                                                    "Legacy interactive mode; reads input from stdin") in
                                                let uu____2742 =
                                                  let uu____2753 =
                                                    let uu____2762 =
                                                      let uu____2763 =
                                                        mk_bool true in
                                                      Const uu____2763 in
                                                    (FStar_Getopt.noshort,
                                                      "ide", uu____2762,
                                                      "JSON-based interactive mode for IDEs") in
                                                  let uu____2764 =
                                                    let uu____2775 =
                                                      let uu____2786 =
                                                        let uu____2795 =
                                                          let uu____2796 =
                                                            mk_bool true in
                                                          Const uu____2796 in
                                                        (FStar_Getopt.noshort,
                                                          "indent",
                                                          uu____2795,
                                                          "Parses and outputs the files on the command line") in
                                                      let uu____2797 =
                                                        let uu____2808 =
                                                          let uu____2819 =
                                                            let uu____2830 =
                                                              let uu____2839
                                                                =
                                                                let uu____2840
                                                                  =
                                                                  mk_bool
                                                                    true in
                                                                Const
                                                                  uu____2840 in
                                                              (FStar_Getopt.noshort,
                                                                "lax",
                                                                uu____2839,
                                                                "Run the lax-type checker only (admit all verification conditions)") in
                                                            let uu____2841 =
                                                              let uu____2852
                                                                =
                                                                let uu____2863
                                                                  =
                                                                  let uu____2872
                                                                    =
                                                                    let uu____2873
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2873 in
                                                                  (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____2872,
                                                                    "Print types computed for data/val/let-bindings") in
                                                                let uu____2874
                                                                  =
                                                                  let uu____2885
                                                                    =
                                                                    let uu____2894
                                                                    =
                                                                    let uu____2895
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2895 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____2894,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go") in
                                                                  let uu____2896
                                                                    =
                                                                    let uu____2907
                                                                    =
                                                                    let uu____2918
                                                                    =
                                                                    let uu____2929
                                                                    =
                                                                    let uu____2940
                                                                    =
                                                                    let uu____2949
                                                                    =
                                                                    let uu____2950
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2950 in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____2949,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)") in
                                                                    let uu____2951
                                                                    =
                                                                    let uu____2962
                                                                    =
                                                                    let uu____2973
                                                                    =
                                                                    let uu____2982
                                                                    =
                                                                    let uu____2983
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____2983 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____2982,
                                                                    "Ignore the default module search paths") in
                                                                    let uu____2984
                                                                    =
                                                                    let uu____2995
                                                                    =
                                                                    let uu____3006
                                                                    =
                                                                    let uu____3015
                                                                    =
                                                                    let uu____3016
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3016 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3015,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)") in
                                                                    let uu____3017
                                                                    =
                                                                    let uu____3028
                                                                    =
                                                                    let uu____3039
                                                                    =
                                                                    let uu____3050
                                                                    =
                                                                    let uu____3059
                                                                    =
                                                                    let uu____3060
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3060 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3059,
                                                                    "Print the types of bound variables") in
                                                                    let uu____3061
                                                                    =
                                                                    let uu____3072
                                                                    =
                                                                    let uu____3081
                                                                    =
                                                                    let uu____3082
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3082 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3081,
                                                                    "Print inferred predicate transformers for all computation types") in
                                                                    let uu____3083
                                                                    =
                                                                    let uu____3094
                                                                    =
                                                                    let uu____3103
                                                                    =
                                                                    let uu____3104
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3104 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3103,
                                                                    "Print full names of variables") in
                                                                    let uu____3105
                                                                    =
                                                                    let uu____3116
                                                                    =
                                                                    let uu____3125
                                                                    =
                                                                    let uu____3126
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3126 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3125,
                                                                    "Print implicit arguments") in
                                                                    let uu____3127
                                                                    =
                                                                    let uu____3138
                                                                    =
                                                                    let uu____3147
                                                                    =
                                                                    let uu____3148
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3148 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3147,
                                                                    "Print universes") in
                                                                    let uu____3149
                                                                    =
                                                                    let uu____3160
                                                                    =
                                                                    let uu____3169
                                                                    =
                                                                    let uu____3170
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3170 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3169,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)") in
                                                                    let uu____3171
                                                                    =
                                                                    let uu____3182
                                                                    =
                                                                    let uu____3191
                                                                    =
                                                                    let uu____3192
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3192 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3191,
                                                                    "Print full names (deprecated; use --print_full_names instead)") in
                                                                    let uu____3193
                                                                    =
                                                                    let uu____3204
                                                                    =
                                                                    let uu____3213
                                                                    =
                                                                    let uu____3214
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3214 in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3213,
                                                                    "Print SMT query statistics") in
                                                                    let uu____3215
                                                                    =
                                                                    let uu____3226
                                                                    =
                                                                    let uu____3235
                                                                    =
                                                                    let uu____3236
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3236 in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3235,
                                                                    "Record a database of hints for efficient proof replay") in
                                                                    let uu____3237
                                                                    =
                                                                    let uu____3248
                                                                    =
                                                                    let uu____3259
                                                                    =
                                                                    let uu____3268
                                                                    =
                                                                    let uu____3269
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3269 in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3268,
                                                                    " ") in
                                                                    let uu____3270
                                                                    =
                                                                    let uu____3281
                                                                    =
                                                                    let uu____3292
                                                                    =
                                                                    let uu____3303
                                                                    =
                                                                    let uu____3314
                                                                    =
                                                                    let uu____3325
                                                                    =
                                                                    let uu____3334
                                                                    =
                                                                    let uu____3335
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3335 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____3334,
                                                                    "Do not use the lexical scope of tactics to improve binder names") in
                                                                    let uu____3336
                                                                    =
                                                                    let uu____3347
                                                                    =
                                                                    let uu____3356
                                                                    =
                                                                    let uu____3357
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3357 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3356,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)") in
                                                                    let uu____3358
                                                                    =
                                                                    let uu____3369
                                                                    =
                                                                    let uu____3380
                                                                    =
                                                                    let uu____3389
                                                                    =
                                                                    let uu____3390
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3390 in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3389,
                                                                    "Print the time it takes to verify each top-level definition") in
                                                                    let uu____3391
                                                                    =
                                                                    let uu____3402
                                                                    =
                                                                    let uu____3411
                                                                    =
                                                                    let uu____3412
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3412 in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3411,
                                                                    "Don't print an error message; show an exception trace instead") in
                                                                    let uu____3413
                                                                    =
                                                                    let uu____3424
                                                                    =
                                                                    let uu____3433
                                                                    =
                                                                    let uu____3434
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3434 in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3433,
                                                                    "Emit output formatted for debugging") in
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
                                                                    "unthrottle_inductives",
                                                                    uu____3455,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)") in
                                                                    let uu____3457
                                                                    =
                                                                    let uu____3468
                                                                    =
                                                                    let uu____3477
                                                                    =
                                                                    let uu____3478
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3478 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____3477,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.") in
                                                                    let uu____3479
                                                                    =
                                                                    let uu____3490
                                                                    =
                                                                    let uu____3499
                                                                    =
                                                                    let uu____3500
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3500 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____3499,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)") in
                                                                    let uu____3501
                                                                    =
                                                                    let uu____3512
                                                                    =
                                                                    let uu____3521
                                                                    =
                                                                    let uu____3522
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3522 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____3521,
                                                                    "Use a previously recorded hints database for proof replay") in
                                                                    let uu____3523
                                                                    =
                                                                    let uu____3534
                                                                    =
                                                                    let uu____3543
                                                                    =
                                                                    let uu____3544
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3544 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____3543,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database") in
                                                                    let uu____3545
                                                                    =
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
                                                                    "no_tactics",
                                                                    uu____3576,
                                                                    "Do not run the tactic engine before discharging a VC") in
                                                                    let uu____3578
                                                                    =
                                                                    let uu____3589
                                                                    =
                                                                    let uu____3600
                                                                    =
                                                                    let uu____3611
                                                                    =
                                                                    let uu____3622
                                                                    =
                                                                    let uu____3632
                                                                    =
                                                                    let uu____3633
                                                                    =
                                                                    let uu____3640
                                                                    =
                                                                    let uu____3641
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3641 in
                                                                    ((fun
                                                                    uu____3646
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____3640) in
                                                                    WithSideEffect
                                                                    uu____3633 in
                                                                    (118,
                                                                    "version",
                                                                    uu____3632,
                                                                    "Display version number") in
                                                                    let uu____3650
                                                                    =
                                                                    let uu____3662
                                                                    =
                                                                    let uu____3671
                                                                    =
                                                                    let uu____3672
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3672 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____3671,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)") in
                                                                    let uu____3673
                                                                    =
                                                                    let uu____3684
                                                                    =
                                                                    let uu____3695
                                                                    =
                                                                    let uu____3704
                                                                    =
                                                                    let uu____3705
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3705 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____3704,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness") in
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
                                                                    let uu____3761
                                                                    =
                                                                    let uu____3770
                                                                    =
                                                                    let uu____3771
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3771 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____3770,
                                                                    "Don't check positivity of inductive types") in
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
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____3792,
                                                                    "Do not eta-expand coertions in generated OCaml") in
                                                                    let uu____3794
                                                                    =
                                                                    let uu____3805
                                                                    =
                                                                    let uu____3816
                                                                    =
                                                                    let uu____3826
                                                                    =
                                                                    let uu____3827
                                                                    =
                                                                    let uu____3834
                                                                    =
                                                                    let uu____3835
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3835 in
                                                                    ((fun
                                                                    uu____3840
                                                                     ->
                                                                    (
                                                                    let uu____3842
                                                                    =
                                                                    specs () in
                                                                    display_usage_aux
                                                                    uu____3842);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    uu____3834) in
                                                                    WithSideEffect
                                                                    uu____3827 in
                                                                    (104,
                                                                    "help",
                                                                    uu____3826,
                                                                    "Display this information") in
                                                                    [uu____3816] in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____3805 in
                                                                    uu____3783
                                                                    ::
                                                                    uu____3794 in
                                                                    uu____3761
                                                                    ::
                                                                    uu____3772 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'false')")
                                                                    ::
                                                                    uu____3750 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____3739 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____3728 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____3717 in
                                                                    uu____3695
                                                                    ::
                                                                    uu____3706 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____3684 in
                                                                    uu____3662
                                                                    ::
                                                                    uu____3673 in
                                                                    uu____3622
                                                                    ::
                                                                    uu____3650 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____3611 in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____3600 in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____3589 in
                                                                    uu____3567
                                                                    ::
                                                                    uu____3578 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____3556 in
                                                                    uu____3534
                                                                    ::
                                                                    uu____3545 in
                                                                    uu____3512
                                                                    ::
                                                                    uu____3523 in
                                                                    uu____3490
                                                                    ::
                                                                    uu____3501 in
                                                                    uu____3468
                                                                    ::
                                                                    uu____3479 in
                                                                    uu____3446
                                                                    ::
                                                                    uu____3457 in
                                                                    uu____3424
                                                                    ::
                                                                    uu____3435 in
                                                                    uu____3402
                                                                    ::
                                                                    uu____3413 in
                                                                    uu____3380
                                                                    ::
                                                                    uu____3391 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3369 in
                                                                    uu____3347
                                                                    ::
                                                                    uu____3358 in
                                                                    uu____3325
                                                                    ::
                                                                    uu____3336 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3314 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3303 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3292 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3281 in
                                                                    uu____3259
                                                                    ::
                                                                    uu____3270 in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3248 in
                                                                    uu____3226
                                                                    ::
                                                                    uu____3237 in
                                                                    uu____3204
                                                                    ::
                                                                    uu____3215 in
                                                                    uu____3182
                                                                    ::
                                                                    uu____3193 in
                                                                    uu____3160
                                                                    ::
                                                                    uu____3171 in
                                                                    uu____3138
                                                                    ::
                                                                    uu____3149 in
                                                                    uu____3116
                                                                    ::
                                                                    uu____3127 in
                                                                    uu____3094
                                                                    ::
                                                                    uu____3105 in
                                                                    uu____3072
                                                                    ::
                                                                    uu____3083 in
                                                                    uu____3050
                                                                    ::
                                                                    uu____3061 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3039 in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3028 in
                                                                    uu____3006
                                                                    ::
                                                                    uu____3017 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____2995 in
                                                                    uu____2973
                                                                    ::
                                                                    uu____2984 in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____2962 in
                                                                    uu____2940
                                                                    ::
                                                                    uu____2951 in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____2929 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____2918 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____2907 in
                                                                  uu____2885
                                                                    ::
                                                                    uu____2896 in
                                                                uu____2863 ::
                                                                  uu____2874 in
                                                              (FStar_Getopt.noshort,
                                                                "load",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "module")),
                                                                "Load compiled module")
                                                                :: uu____2852 in
                                                            uu____2830 ::
                                                              uu____2841 in
                                                          (FStar_Getopt.noshort,
                                                            "initial_ifuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                            :: uu____2819 in
                                                        (FStar_Getopt.noshort,
                                                          "initial_fuel",
                                                          (IntStr
                                                             "non-negative integer"),
                                                          "Number of unrolling of recursive functions to try initially (default 2)")
                                                          :: uu____2808 in
                                                      uu____2786 ::
                                                        uu____2797 in
                                                    (FStar_Getopt.noshort,
                                                      "include",
                                                      (ReverseAccumulated
                                                         (PathStr "path")),
                                                      "A directory in which to search for files included on the command line")
                                                      :: uu____2775 in
                                                  uu____2753 :: uu____2764 in
                                                uu____2731 :: uu____2742 in
                                              uu____2709 :: uu____2720 in
                                            (FStar_Getopt.noshort,
                                              "hint_file", (PathStr "path"),
                                              "Read/write hints to <path> (instead of module-specific hints files)")
                                              :: uu____2698 in
                                          uu____2676 :: uu____2687 in
                                        (FStar_Getopt.noshort,
                                          "gen_native_tactics",
                                          (PathStr "[path]"),
                                          "Compile all user tactics used in the module in <path>")
                                          :: uu____2665 in
                                      (FStar_Getopt.noshort, "fstar_home",
                                        (PathStr "dir"),
                                        "Set the FSTAR_HOME variable to <dir>")
                                        :: uu____2654 in
                                    uu____2632 :: uu____2643 in
                                  (FStar_Getopt.noshort, "extract_namespace",
                                    (Accumulated
                                       (PostProcessed
                                          (pp_lowercase,
                                            (SimpleStr "namespace name")))),
                                    "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                    :: uu____2621 in
                                (FStar_Getopt.noshort, "extract_module",
                                  (Accumulated
                                     (PostProcessed
                                        (pp_lowercase,
                                          (SimpleStr "module_name")))),
                                  "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                  :: uu____2610 in
                              (FStar_Getopt.noshort, "extract",
                                (Accumulated
                                   (SimpleStr
                                      "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                :: uu____2599 in
                            uu____2577 :: uu____2588 in
                          (FStar_Getopt.noshort, "dump_module",
                            (Accumulated (SimpleStr "module_name")), "") ::
                            uu____2566 in
                        uu____2544 :: uu____2555 in
                      uu____2522 :: uu____2533 in
                    uu____2500 :: uu____2511 in
                  (FStar_Getopt.noshort, "dep",
                    (EnumStr ["make"; "graph"; "full"]),
                    "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                    :: uu____2489 in
                (FStar_Getopt.noshort, "debug_level",
                  (Accumulated
                     (OpenEnumStr
                        (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                  "Control the verbosity of debugging info") :: uu____2478 in
              (FStar_Getopt.noshort, "debug",
                (Accumulated (SimpleStr "module_name")),
                "Print lots of debugging information while checking module")
                :: uu____2467 in
            (FStar_Getopt.noshort, "codegen-lib",
              (Accumulated (SimpleStr "namespace")),
              "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
              :: uu____2456 in
          (FStar_Getopt.noshort, "codegen",
            (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "tactics"]),
            "Generate code for execution") :: uu____2445 in
        uu____2423 :: uu____2434 in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2412 in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2401
and specs: Prims.unit -> FStar_Getopt.opt Prims.list =
  fun uu____4556  ->
    let uu____4559 = specs_with_types () in
    FStar_List.map
      (fun uu____4584  ->
         match uu____4584 with
         | (short,long,typ,doc) ->
             let uu____4597 =
               let uu____4608 = arg_spec_of_opt_type long typ in
               (short, long, uu____4608, doc) in
             mk_spec uu____4597) uu____4559
let settable: Prims.string -> Prims.bool =
  fun uu___40_4615  ->
    match uu___40_4615 with
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
    | uu____4616 -> false
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
       (fun uu____4673  ->
          match uu____4673 with
          | (uu____4684,x,uu____4686,uu____4687) -> settable x))
let resettable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____4733  ->
          match uu____4733 with
          | (uu____4744,x,uu____4746,uu____4747) -> resettable x))
let display_usage: Prims.unit -> Prims.unit =
  fun uu____4754  ->
    let uu____4755 = specs () in display_usage_aux uu____4755
let fstar_home: Prims.unit -> Prims.string =
  fun uu____4770  ->
    let uu____4771 = get_fstar_home () in
    match uu____4771 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        ((let uu____4777 =
            let uu____4782 = mk_string x1 in ("fstar_home", uu____4782) in
          set_option' uu____4777);
         x1)
    | FStar_Pervasives_Native.Some x -> x
exception File_argument of Prims.string
let uu___is_File_argument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____4790 -> true
    | uu____4791 -> false
let __proj__File_argument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____4798 -> uu____4798
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
          let uu____4842 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____4842
let file_list_: Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let parse_cmd_line:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____4868  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____4873 =
             let uu____4876 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____4876 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____4873) in
    let uu____4925 =
      let uu____4928 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____4928 in
    (res, uu____4925)
let file_list: Prims.unit -> Prims.string Prims.list =
  fun uu____4960  -> FStar_ST.op_Bang file_list_
let restore_cmd_line_options: Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____4993 = specs () in
       FStar_Getopt.parse_cmdline uu____4993 (fun x  -> ()) in
     (let uu____4999 =
        let uu____5004 =
          let uu____5005 = FStar_List.map mk_string old_verify_module in
          List uu____5005 in
        ("verify_module", uu____5004) in
      set_option' uu____4999);
     r)
let module_name_of_file_name: Prims.string -> Prims.string =
  fun f  ->
    let f1 = FStar_Util.basename f in
    let f2 =
      let uu____5013 =
        let uu____5014 =
          let uu____5015 =
            let uu____5016 = FStar_Util.get_file_extension f1 in
            FStar_String.length uu____5016 in
          (FStar_String.length f1) - uu____5015 in
        uu____5014 - (Prims.parse_int "1") in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5013 in
    FStar_String.lowercase f2
let should_verify: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5020 = get_lax () in
    if uu____5020
    then false
    else
      (let l = get_verify_module () in
       FStar_List.contains (FStar_String.lowercase m) l)
let should_verify_file: Prims.string -> Prims.bool =
  fun fn  ->
    let uu____5028 = module_name_of_file_name fn in should_verify uu____5028
let dont_gen_projectors: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5032 = get___temp_no_proj () in
    FStar_List.contains m uu____5032
let should_print_message: Prims.string -> Prims.bool =
  fun m  ->
    let uu____5038 = should_verify m in
    if uu____5038 then m <> "Prims" else false
let include_path: Prims.unit -> Prims.string Prims.list =
  fun uu____5044  ->
    let uu____5045 = get_no_default_includes () in
    if uu____5045
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____5053 =
         let uu____5056 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____5056
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____5069 =
         let uu____5072 = get_include () in
         FStar_List.append uu____5072 ["."] in
       FStar_List.append uu____5053 uu____5069)
let find_file: Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____5080 = FStar_Util.is_path_absolute filename in
    if uu____5080
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5087 =
         let uu____5090 = include_path () in FStar_List.rev uu____5090 in
       FStar_Util.find_map uu____5087
         (fun p  ->
            let path = FStar_Util.join_paths p filename in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
let prims: Prims.unit -> Prims.string =
  fun uu____5102  ->
    let uu____5103 = get_prims () in
    match uu____5103 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst" in
        let uu____5107 = find_file filename in
        (match uu____5107 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5111 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename in
             failwith uu____5111)
    | FStar_Pervasives_Native.Some x -> x
let prims_basename: Prims.unit -> Prims.string =
  fun uu____5115  ->
    let uu____5116 = prims () in FStar_Util.basename uu____5116
let pervasives: Prims.unit -> Prims.string =
  fun uu____5119  ->
    let filename = "FStar.Pervasives.fst" in
    let uu____5121 = find_file filename in
    match uu____5121 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5125 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5125
let pervasives_basename: Prims.unit -> Prims.string =
  fun uu____5128  ->
    let uu____5129 = pervasives () in FStar_Util.basename uu____5129
let pervasives_native_basename: Prims.unit -> Prims.string =
  fun uu____5132  ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____5134 = find_file filename in
    match uu____5134 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5138 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____5138
let prepend_output_dir: Prims.string -> Prims.string =
  fun fname  ->
    let uu____5142 = get_odir () in
    match uu____5142 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
let parse_setting:
  Prims.string ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list
  =
  fun s  ->
    let parse_one_setting s1 =
      if s1 = "*"
      then ([], true)
      else
        if FStar_Util.starts_with s1 "-"
        then
          (let path =
             let uu____5193 =
               FStar_Util.substring_from s1 (Prims.parse_int "1") in
             FStar_Ident.path_of_text uu____5193 in
           (path, false))
        else
          (let s2 =
             if FStar_Util.starts_with s1 "+"
             then FStar_Util.substring_from s1 (Prims.parse_int "1")
             else s1 in
           ((FStar_Ident.path_of_text s2), true)) in
    FStar_All.pipe_right (FStar_Util.split s " ")
      (FStar_List.map parse_one_setting)
let __temp_no_proj: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5220 = get___temp_no_proj () in
    FStar_All.pipe_right uu____5220 (FStar_List.contains s)
let admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____5227  -> get_admit_smt_queries ()
let admit_except: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5232  -> get_admit_except ()
let cache_checked_modules: Prims.unit -> Prims.bool =
  fun uu____5235  -> get_cache_checked_modules ()
let codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5240  -> get_codegen ()
let codegen_libs: Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____5247  ->
    let uu____5248 = get_codegen_lib () in
    FStar_All.pipe_right uu____5248
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
let debug_any: Prims.unit -> Prims.bool =
  fun uu____5263  -> let uu____5264 = get_debug () in uu____5264 <> []
let debug_at_level: Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      (let uu____5277 = get_debug () in
       FStar_All.pipe_right uu____5277 (FStar_List.contains modul)) &&
        (debug_level_geq level)
let dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5286  -> get_dep ()
let detail_errors: Prims.unit -> Prims.bool =
  fun uu____5289  -> get_detail_errors ()
let detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____5292  -> get_detail_hint_replay ()
let doc: Prims.unit -> Prims.bool = fun uu____5295  -> get_doc ()
let dump_module: Prims.string -> Prims.bool =
  fun s  ->
    let uu____5299 = get_dump_module () in
    FStar_All.pipe_right uu____5299 (FStar_List.contains s)
let eager_inference: Prims.unit -> Prims.bool =
  fun uu____5306  -> get_eager_inference ()
let expose_interfaces: Prims.unit -> Prims.bool =
  fun uu____5309  -> get_expose_interfaces ()
let fs_typ_app: Prims.string -> Prims.bool =
  fun filename  ->
    let uu____5313 = FStar_ST.op_Bang light_off_files in
    FStar_List.contains filename uu____5313
let gen_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5343  -> get_gen_native_tactics ()
let full_context_dependency: Prims.unit -> Prims.bool =
  fun uu____5346  -> true
let hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____5349  -> get_hide_uvar_nums ()
let hint_info: Prims.unit -> Prims.bool =
  fun uu____5352  -> (get_hint_info ()) || (get_query_stats ())
let hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5357  -> get_hint_file ()
let ide: Prims.unit -> Prims.bool = fun uu____5360  -> get_ide ()
let indent: Prims.unit -> Prims.bool = fun uu____5363  -> get_indent ()
let initial_fuel: Prims.unit -> Prims.int =
  fun uu____5366  ->
    let uu____5367 = get_initial_fuel () in
    let uu____5368 = get_max_fuel () in Prims.min uu____5367 uu____5368
let initial_ifuel: Prims.unit -> Prims.int =
  fun uu____5371  ->
    let uu____5372 = get_initial_ifuel () in
    let uu____5373 = get_max_ifuel () in Prims.min uu____5372 uu____5373
let interactive: Prims.unit -> Prims.bool =
  fun uu____5376  -> (get_in ()) || (get_ide ())
let lax: Prims.unit -> Prims.bool = fun uu____5379  -> get_lax ()
let load: Prims.unit -> Prims.string Prims.list =
  fun uu____5384  -> get_load ()
let legacy_interactive: Prims.unit -> Prims.bool =
  fun uu____5387  -> get_in ()
let log_queries: Prims.unit -> Prims.bool =
  fun uu____5390  -> get_log_queries ()
let log_types: Prims.unit -> Prims.bool = fun uu____5393  -> get_log_types ()
let max_fuel: Prims.unit -> Prims.int = fun uu____5396  -> get_max_fuel ()
let max_ifuel: Prims.unit -> Prims.int = fun uu____5399  -> get_max_ifuel ()
let min_fuel: Prims.unit -> Prims.int = fun uu____5402  -> get_min_fuel ()
let ml_ish: Prims.unit -> Prims.bool = fun uu____5405  -> get_MLish ()
let set_ml_ish: Prims.unit -> Prims.unit =
  fun uu____5408  -> set_option "MLish" (Bool true)
let n_cores: Prims.unit -> Prims.int = fun uu____5411  -> get_n_cores ()
let no_default_includes: Prims.unit -> Prims.bool =
  fun uu____5414  -> get_no_default_includes ()
let no_extract: Prims.string -> Prims.bool =
  fun s  ->
    let s1 = FStar_String.lowercase s in
    let uu____5419 = get_no_extract () in
    FStar_All.pipe_right uu____5419
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
let no_location_info: Prims.unit -> Prims.bool =
  fun uu____5428  -> get_no_location_info ()
let output_dir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5433  -> get_odir ()
let ugly: Prims.unit -> Prims.bool = fun uu____5436  -> get_ugly ()
let print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____5439  -> get_print_bound_var_types ()
let print_effect_args: Prims.unit -> Prims.bool =
  fun uu____5442  -> get_print_effect_args ()
let print_implicits: Prims.unit -> Prims.bool =
  fun uu____5445  -> get_print_implicits ()
let print_real_names: Prims.unit -> Prims.bool =
  fun uu____5448  -> (get_prn ()) || (get_print_full_names ())
let print_universes: Prims.unit -> Prims.bool =
  fun uu____5451  -> get_print_universes ()
let print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____5454  -> (get_print_z3_statistics ()) || (get_query_stats ())
let query_stats: Prims.unit -> Prims.bool =
  fun uu____5457  -> get_query_stats ()
let record_hints: Prims.unit -> Prims.bool =
  fun uu____5460  -> get_record_hints ()
let reuse_hint_for: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____5465  -> get_reuse_hint_for ()
let silent: Prims.unit -> Prims.bool = fun uu____5468  -> get_silent ()
let smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____5471  -> get_smtencoding_elim_box ()
let smtencoding_nl_arith_native: Prims.unit -> Prims.bool =
  fun uu____5474  ->
    let uu____5475 = get_smtencoding_nl_arith_repr () in
    uu____5475 = "native"
let smtencoding_nl_arith_wrapped: Prims.unit -> Prims.bool =
  fun uu____5478  ->
    let uu____5479 = get_smtencoding_nl_arith_repr () in
    uu____5479 = "wrapped"
let smtencoding_nl_arith_default: Prims.unit -> Prims.bool =
  fun uu____5482  ->
    let uu____5483 = get_smtencoding_nl_arith_repr () in
    uu____5483 = "boxwrap"
let smtencoding_l_arith_native: Prims.unit -> Prims.bool =
  fun uu____5486  ->
    let uu____5487 = get_smtencoding_l_arith_repr () in uu____5487 = "native"
let smtencoding_l_arith_default: Prims.unit -> Prims.bool =
  fun uu____5490  ->
    let uu____5491 = get_smtencoding_l_arith_repr () in
    uu____5491 = "boxwrap"
let tactic_raw_binders: Prims.unit -> Prims.bool =
  fun uu____5494  -> get_tactic_raw_binders ()
let tactic_trace: Prims.unit -> Prims.bool =
  fun uu____5497  -> get_tactic_trace ()
let tactic_trace_d: Prims.unit -> Prims.int =
  fun uu____5500  -> get_tactic_trace_d ()
let timing: Prims.unit -> Prims.bool = fun uu____5503  -> get_timing ()
let trace_error: Prims.unit -> Prims.bool =
  fun uu____5506  -> get_trace_error ()
let unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____5509  -> get_unthrottle_inductives ()
let unsafe_tactic_exec: Prims.unit -> Prims.bool =
  fun uu____5512  -> get_unsafe_tactic_exec ()
let use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____5515  -> get_use_eq_at_higher_order ()
let use_hints: Prims.unit -> Prims.bool = fun uu____5518  -> get_use_hints ()
let use_hint_hashes: Prims.unit -> Prims.bool =
  fun uu____5521  -> get_use_hint_hashes ()
let use_native_tactics:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____5526  -> get_use_native_tactics ()
let use_tactics: Prims.unit -> Prims.bool =
  fun uu____5529  -> get_use_tactics ()
let using_facts_from:
  Prims.unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5538  ->
    let uu____5539 = get_using_facts_from () in
    match uu____5539 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns ->
        let uu____5571 = FStar_List.collect parse_setting ns in
        FStar_All.pipe_right uu____5571 FStar_List.rev
let vcgen_optimize_bind_as_seq: Prims.unit -> Prims.bool =
  fun uu____5610  ->
    let uu____5611 = get_vcgen_optimize_bind_as_seq () in
    FStar_Option.isSome uu____5611
let vcgen_decorate_with_type: Prims.unit -> Prims.bool =
  fun uu____5616  ->
    let uu____5617 = get_vcgen_optimize_bind_as_seq () in
    match uu____5617 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____5620 -> false
let warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____5625  -> get_warn_default_effects ()
let z3_exe: Prims.unit -> Prims.string =
  fun uu____5628  ->
    let uu____5629 = get_smt () in
    match uu____5629 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let z3_cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____5637  -> get_z3cliopt ()
let z3_refresh: Prims.unit -> Prims.bool =
  fun uu____5640  -> get_z3refresh ()
let z3_rlimit: Prims.unit -> Prims.int = fun uu____5643  -> get_z3rlimit ()
let z3_rlimit_factor: Prims.unit -> Prims.int =
  fun uu____5646  -> get_z3rlimit_factor ()
let z3_seed: Prims.unit -> Prims.int = fun uu____5649  -> get_z3seed ()
let use_two_phase_tc: Prims.unit -> Prims.bool =
  fun uu____5652  -> get_use_two_phase_tc ()
let no_positivity: Prims.unit -> Prims.bool =
  fun uu____5655  -> get_no_positivity ()
let ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____5658  -> get_ml_no_eta_expand_coertions ()
let warn_error: Prims.unit -> Prims.string =
  fun uu____5661  -> get_warn_error ()
let should_extract: Prims.string -> Prims.bool =
  fun m  ->
    let m1 = FStar_String.lowercase m in
    let uu____5666 = get_extract () in
    match uu____5666 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____5671 =
            let uu____5684 = get_no_extract () in
            let uu____5687 = get_extract_namespace () in
            let uu____5690 = get_extract_module () in
            (uu____5684, uu____5687, uu____5690) in
          match uu____5671 with
          | ([],[],[]) -> ()
          | uu____5705 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting =
            let uu____5727 = parse_setting extract_setting in
            FStar_All.pipe_right uu____5727 FStar_List.rev in
          let m_components = FStar_Ident.path_of_text m1 in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____5780,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____5799 -> false in
          let uu____5808 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____5842  ->
                    match uu____5842 with
                    | (path,uu____5850) -> matches_path m_components path)) in
          match uu____5808 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____5861,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____5877 = get_extract_namespace () in
          match uu____5877 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1))) in
        let should_extract_module m2 =
          let uu____5891 = get_extract_module () in
          match uu____5891 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2)) in
        (let uu____5903 = no_extract m1 in Prims.op_Negation uu____5903) &&
          (let uu____5905 =
             let uu____5914 = get_extract_namespace () in
             let uu____5917 = get_extract_module () in
             (uu____5914, uu____5917) in
           (match uu____5905 with
            | ([],[]) -> true
            | uu____5928 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
let codegen_fsharp: Prims.unit -> Prims.bool =
  fun uu____5939  ->
    let uu____5940 = codegen () in
    uu____5940 = (FStar_Pervasives_Native.Some "FSharp")