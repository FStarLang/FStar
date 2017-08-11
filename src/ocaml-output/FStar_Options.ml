open Prims
type debug_level_t =
  | Low
  | Medium
  | High
  | Extreme
  | Other of Prims.string
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
  | Unset
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
  | Restore
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
  fun uu____202  -> FStar_ST.op_Colon_Equals __unit_tests__ true
let __clear_unit_tests: Prims.unit -> Prims.unit =
  fun uu____216  -> FStar_ST.op_Colon_Equals __unit_tests__ false
let as_bool: option_val -> Prims.bool =
  fun uu___49_230  ->
    match uu___49_230 with
    | Bool b -> b
    | uu____232 -> failwith "Impos: expected Bool"
let as_int: option_val -> Prims.int =
  fun uu___50_236  ->
    match uu___50_236 with
    | Int b -> b
    | uu____238 -> failwith "Impos: expected Int"
let as_string: option_val -> Prims.string =
  fun uu___51_242  ->
    match uu___51_242 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____245 -> failwith "Impos: expected String"
let as_list:
  'Auu____252 .
    (option_val -> 'Auu____252) -> option_val -> 'Auu____252 Prims.list
  =
  fun as_t  ->
    fun uu___52_265  ->
      match uu___52_265 with
      | List ts -> FStar_All.pipe_right ts (FStar_List.map as_t)
      | uu____275 -> failwith "Impos: expected List"
let as_option:
  'Auu____284 .
    (option_val -> 'Auu____284) ->
      option_val -> 'Auu____284 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___53_297  ->
      match uu___53_297 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____301 = as_t v1 in FStar_Pervasives_Native.Some uu____301
type optionstate = option_val FStar_Util.smap
let fstar_options: optionstate Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let peek: Prims.unit -> optionstate =
  fun uu____320  ->
    let uu____321 = FStar_ST.op_Bang fstar_options in FStar_List.hd uu____321
let pop: Prims.unit -> Prims.unit =
  fun uu____345  ->
    let uu____346 = FStar_ST.op_Bang fstar_options in
    match uu____346 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____367::[] -> failwith "TOO MANY POPS!"
    | uu____368::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
let push: Prims.unit -> Prims.unit =
  fun uu____393  ->
    let uu____394 =
      let uu____397 =
        let uu____400 = peek () in FStar_Util.smap_copy uu____400 in
      let uu____403 = FStar_ST.op_Bang fstar_options in uu____397 ::
        uu____403 in
    FStar_ST.op_Colon_Equals fstar_options uu____394
let set: optionstate -> Prims.unit =
  fun o  ->
    let uu____450 = FStar_ST.op_Bang fstar_options in
    match uu____450 with
    | [] -> failwith "set on empty option stack"
    | uu____471::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
let set_option: Prims.string -> option_val -> Prims.unit =
  fun k  ->
    fun v1  -> let uu____501 = peek () in FStar_Util.smap_add uu____501 k v1
let set_option':
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> Prims.unit =
  fun uu____511  -> match uu____511 with | (k,v1) -> set_option k v1
let with_saved_options: 'a . (Prims.unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f () in pop (); retv)
let light_off_files: Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let add_light_off_file: Prims.string -> Prims.unit =
  fun filename  ->
    let uu____552 =
      let uu____555 = FStar_ST.op_Bang light_off_files in filename ::
        uu____555 in
    FStar_ST.op_Colon_Equals light_off_files uu____552
let defaults:
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 Prims.list =
  [("__temp_no_proj", (List []));
  ("_fstar_home", (String ""));
  ("_include_path", (List []));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
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
  ("record_hints", (Bool false));
  ("reuse_hint_for", Unset);
  ("show_signatures", (List []));
  ("silent", (Bool false));
  ("smt", Unset);
  ("smtencoding.elim_box", (Bool false));
  ("smtencoding.nl_arith_repr", (String "boxwrap"));
  ("smtencoding.l_arith_repr", (String "boxwrap"));
  ("split_cases", (Int (Prims.parse_int "0")));
  ("timing", (Bool false));
  ("trace_error", (Bool false));
  ("ugly", (Bool false));
  ("unthrottle_inductives", (Bool false));
  ("use_eq_at_higher_order", (Bool false));
  ("use_hints", (Bool false));
  ("no_tactics", (Bool false));
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
  fun uu____939  ->
    let o = peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let clear: Prims.unit -> Prims.unit =
  fun uu____955  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50") in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
let _run: Prims.unit = clear ()
let get_option: Prims.string -> option_val =
  fun s  ->
    let uu____1005 =
      let uu____1008 = peek () in FStar_Util.smap_try_find uu____1008 s in
    match uu____1005 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
let lookup_opt:
  'Auu____1018 . Prims.string -> (option_val -> 'Auu____1018) -> 'Auu____1018
  = fun s  -> fun c  -> c (get_option s)
let get_admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____1035  -> lookup_opt "admit_smt_queries" as_bool
let get_admit_except:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1041  -> lookup_opt "admit_except" (as_option as_string)
let get_codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1049  -> lookup_opt "codegen" (as_option as_string)
let get_codegen_lib: Prims.unit -> Prims.string Prims.list =
  fun uu____1057  -> lookup_opt "codegen-lib" (as_list as_string)
let get_debug: Prims.unit -> Prims.string Prims.list =
  fun uu____1065  -> lookup_opt "debug" (as_list as_string)
let get_debug_level: Prims.unit -> Prims.string Prims.list =
  fun uu____1073  -> lookup_opt "debug_level" (as_list as_string)
let get_dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1081  -> lookup_opt "dep" (as_option as_string)
let get_detail_errors: Prims.unit -> Prims.bool =
  fun uu____1087  -> lookup_opt "detail_errors" as_bool
let get_detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____1091  -> lookup_opt "detail_hint_replay" as_bool
let get_doc: Prims.unit -> Prims.bool =
  fun uu____1095  -> lookup_opt "doc" as_bool
let get_dump_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1101  -> lookup_opt "dump_module" (as_list as_string)
let get_eager_inference: Prims.unit -> Prims.bool =
  fun uu____1107  -> lookup_opt "eager_inference" as_bool
let get_explicit_deps: Prims.unit -> Prims.bool =
  fun uu____1111  -> lookup_opt "explicit_deps" as_bool
let get_extract_all: Prims.unit -> Prims.bool =
  fun uu____1115  -> lookup_opt "extract_all" as_bool
let get_extract_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1121  -> lookup_opt "extract_module" (as_list as_string)
let get_extract_namespace: Prims.unit -> Prims.string Prims.list =
  fun uu____1129  -> lookup_opt "extract_namespace" (as_list as_string)
let get_fs_typ_app: Prims.unit -> Prims.bool =
  fun uu____1135  -> lookup_opt "fs_typ_app" as_bool
let get_fstar_home: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1141  -> lookup_opt "fstar_home" (as_option as_string)
let get_hide_genident_nums: Prims.unit -> Prims.bool =
  fun uu____1147  -> lookup_opt "hide_genident_nums" as_bool
let get_hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____1151  -> lookup_opt "hide_uvar_nums" as_bool
let get_hint_info: Prims.unit -> Prims.bool =
  fun uu____1155  -> lookup_opt "hint_info" as_bool
let get_hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____1161  -> lookup_opt "hint_file" (as_option as_string)
let get_in: Prims.unit -> Prims.bool =
  fun uu____1167  -> lookup_opt "in" as_bool
let get_ide: Prims.unit -> Prims.bool =
  fun uu____1171  -> lookup_opt "ide" as_bool
let get_include: Prims.unit -> Prims.string Prims.list =
  fun uu____1177  -> lookup_opt "include" (as_list as_string)
let get_indent: Prims.unit -> Prims.bool =
  fun uu____1183  -> lookup_opt "indent" as_bool
let get_initial_fuel: Prims.unit -> Prims.int =
  fun uu____1187  -> lookup_opt "initial_fuel" as_int
let get_initial_ifuel: Prims.unit -> Prims.int =
  fun uu____1191  -> lookup_opt "initial_ifuel" as_int
let get_lax: Prims.unit -> Prims.bool =
  fun uu____1195  -> lookup_opt "lax" as_bool
let get_load: Prims.unit -> Prims.string Prims.list =
  fun uu____1201  -> lookup_opt "load" (as_list as_string)
let get_log_queries: Prims.unit -> Prims.bool =
  fun uu____1207  -> lookup_opt "log_queries" as_bool
let get_log_types: Prims.unit -> Prims.bool =
  fun uu____1211  -> lookup_opt "log_types" as_bool
let get_max_fuel: Prims.unit -> Prims.int =
  fun uu____1215  -> lookup_opt "max_fuel" as_int
let get_max_ifuel: Prims.unit -> Prims.int =
  fun uu____1219  -> lookup_opt "max_ifuel" as_int
let get_min_fuel: Prims.unit -> Prims.int =
  fun uu____1223  -> lookup_opt "min_fuel" as_int
let get_MLish: Prims.unit -> Prims.bool =
  fun uu____1227  -> lookup_opt "MLish" as_bool
let get_n_cores: Prims.unit -> Prims.int =
  fun uu____1231  -> lookup_opt "n_cores" as_int
let get_no_default_includes: Prims.unit -> Prims.bool =
  fun uu____1235  -> lookup_opt "no_default_includes" as_bool
let get_no_extract: Prims.unit -> Prims.string Prims.list =
  fun uu____1241  -> lookup_opt "no_extract" (as_list as_string)
let get_no_location_info: Prims.unit -> Prims.bool =
  fun uu____1247  -> lookup_opt "no_location_info" as_bool
let get_odir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1253  -> lookup_opt "odir" (as_option as_string)
let get_ugly: Prims.unit -> Prims.bool =
  fun uu____1259  -> lookup_opt "ugly" as_bool
let get_prims: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1265  -> lookup_opt "prims" (as_option as_string)
let get_print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____1271  -> lookup_opt "print_bound_var_types" as_bool
let get_print_effect_args: Prims.unit -> Prims.bool =
  fun uu____1275  -> lookup_opt "print_effect_args" as_bool
let get_print_full_names: Prims.unit -> Prims.bool =
  fun uu____1279  -> lookup_opt "print_full_names" as_bool
let get_print_implicits: Prims.unit -> Prims.bool =
  fun uu____1283  -> lookup_opt "print_implicits" as_bool
let get_print_universes: Prims.unit -> Prims.bool =
  fun uu____1287  -> lookup_opt "print_universes" as_bool
let get_print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____1291  -> lookup_opt "print_z3_statistics" as_bool
let get_prn: Prims.unit -> Prims.bool =
  fun uu____1295  -> lookup_opt "prn" as_bool
let get_record_hints: Prims.unit -> Prims.bool =
  fun uu____1299  -> lookup_opt "record_hints" as_bool
let get_reuse_hint_for:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1305  -> lookup_opt "reuse_hint_for" (as_option as_string)
let get_show_signatures: Prims.unit -> Prims.string Prims.list =
  fun uu____1313  -> lookup_opt "show_signatures" (as_list as_string)
let get_silent: Prims.unit -> Prims.bool =
  fun uu____1319  -> lookup_opt "silent" as_bool
let get_smt: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____1325  -> lookup_opt "smt" (as_option as_string)
let get_smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____1331  -> lookup_opt "smtencoding.elim_box" as_bool
let get_smtencoding_nl_arith_repr: Prims.unit -> Prims.string =
  fun uu____1335  -> lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr: Prims.unit -> Prims.string =
  fun uu____1339  -> lookup_opt "smtencoding.l_arith_repr" as_string
let get_split_cases: Prims.unit -> Prims.int =
  fun uu____1343  -> lookup_opt "split_cases" as_int
let get_timing: Prims.unit -> Prims.bool =
  fun uu____1347  -> lookup_opt "timing" as_bool
let get_trace_error: Prims.unit -> Prims.bool =
  fun uu____1351  -> lookup_opt "trace_error" as_bool
let get_unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____1355  -> lookup_opt "unthrottle_inductives" as_bool
let get_use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____1359  -> lookup_opt "use_eq_at_higher_order" as_bool
let get_use_hints: Prims.unit -> Prims.bool =
  fun uu____1363  -> lookup_opt "use_hints" as_bool
let get_use_tactics: Prims.unit -> Prims.bool =
  fun uu____1367  ->
    let uu____1368 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____1368
let get_using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____1376  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let get_verify_all: Prims.unit -> Prims.bool =
  fun uu____1386  -> lookup_opt "verify_all" as_bool
let get_verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____1392  -> lookup_opt "verify_module" (as_list as_string)
let get___temp_no_proj: Prims.unit -> Prims.string Prims.list =
  fun uu____1400  -> lookup_opt "__temp_no_proj" (as_list as_string)
let get_version: Prims.unit -> Prims.bool =
  fun uu____1406  -> lookup_opt "version" as_bool
let get_warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____1410  -> lookup_opt "warn_default_effects" as_bool
let get_z3cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____1416  -> lookup_opt "z3cliopt" (as_list as_string)
let get_z3refresh: Prims.unit -> Prims.bool =
  fun uu____1422  -> lookup_opt "z3refresh" as_bool
let get_z3rlimit: Prims.unit -> Prims.int =
  fun uu____1426  -> lookup_opt "z3rlimit" as_int
let get_z3rlimit_factor: Prims.unit -> Prims.int =
  fun uu____1430  -> lookup_opt "z3rlimit_factor" as_int
let get_z3seed: Prims.unit -> Prims.int =
  fun uu____1434  -> lookup_opt "z3seed" as_int
let get_no_positivity: Prims.unit -> Prims.bool =
  fun uu____1438  -> lookup_opt "__no_positivity" as_bool
let get_ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____1442  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool
let dlevel: Prims.string -> debug_level_t =
  fun uu___54_1446  ->
    match uu___54_1446 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let one_debug_level_geq: debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1456 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let debug_level_geq: debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____1461 = get_debug_level () in
    FStar_All.pipe_right uu____1461
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
let universe_include_path_base_dirs: Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"]
let _version: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _platform: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _compiler: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _date: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _commit: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let display_version: Prims.unit -> Prims.unit =
  fun uu____1553  ->
    let uu____1554 =
      let uu____1555 = FStar_ST.op_Bang _version in
      let uu____1566 = FStar_ST.op_Bang _platform in
      let uu____1577 = FStar_ST.op_Bang _compiler in
      let uu____1588 = FStar_ST.op_Bang _date in
      let uu____1599 = FStar_ST.op_Bang _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1555
        uu____1566 uu____1577 uu____1588 uu____1599 in
    FStar_Util.print_string uu____1554
let display_usage_aux:
  'Auu____1616 'Auu____1617 .
    ('Auu____1617,Prims.string,'Auu____1616 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____1664  ->
         match uu____1664 with
         | (uu____1675,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____1686 =
                      let uu____1687 = FStar_Util.colorize_bold flag in
                      FStar_Util.format1 "  --%s\n" uu____1687 in
                    FStar_Util.print_string uu____1686
                  else
                    (let uu____1689 =
                       let uu____1690 = FStar_Util.colorize_bold flag in
                       FStar_Util.format2 "  --%s  %s\n" uu____1690 doc in
                     FStar_Util.print_string uu____1689)
              | FStar_Getopt.OneArg (uu____1691,argname) ->
                  if doc = ""
                  then
                    let uu____1697 =
                      let uu____1698 = FStar_Util.colorize_bold flag in
                      let uu____1699 = FStar_Util.colorize_bold argname in
                      FStar_Util.format2 "  --%s %s\n" uu____1698 uu____1699 in
                    FStar_Util.print_string uu____1697
                  else
                    (let uu____1701 =
                       let uu____1702 = FStar_Util.colorize_bold flag in
                       let uu____1703 = FStar_Util.colorize_bold argname in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____1702
                         uu____1703 doc in
                     FStar_Util.print_string uu____1701))) specs
let mk_spec:
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____1728 = o in
    match uu____1728 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____1758 =
                let uu____1759 = let uu____1764 = f () in (name, uu____1764) in
                set_option' uu____1759 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x =
                let uu____1775 = let uu____1780 = f x in (name, uu____1780) in
                set_option' uu____1775 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let cons_extract_module: Prims.string -> option_val =
  fun s  ->
    let uu____1789 =
      let uu____1792 =
        let uu____1795 = get_extract_module () in (FStar_String.lowercase s)
          :: uu____1795 in
      FStar_All.pipe_right uu____1792
        (FStar_List.map (fun _0_33  -> String _0_33)) in
    List uu____1789
let cons_extract_namespace: Prims.string -> option_val =
  fun s  ->
    let uu____1806 =
      let uu____1809 =
        let uu____1812 = get_extract_namespace () in
        (FStar_String.lowercase s) :: uu____1812 in
      FStar_All.pipe_right uu____1809
        (FStar_List.map (fun _0_34  -> String _0_34)) in
    List uu____1806
let add_extract_module: Prims.string -> Prims.unit =
  fun s  ->
    let uu____1823 = cons_extract_module s in
    set_option "extract_module" uu____1823
let add_extract_namespace: Prims.string -> Prims.unit =
  fun s  ->
    let uu____1828 = cons_extract_namespace s in
    set_option "extract_namespace" uu____1828
let cons_verify_module: Prims.string -> option_val =
  fun s  ->
    let uu____1833 =
      let uu____1836 =
        let uu____1839 = get_verify_module () in (FStar_String.lowercase s)
          :: uu____1839 in
      FStar_All.pipe_right uu____1836
        (FStar_List.map (fun _0_35  -> String _0_35)) in
    List uu____1833
let cons_using_facts_from: Prims.string -> option_val =
  fun s  ->
    set_option "z3refresh" (Bool true);
    (let uu____1851 = get_using_facts_from () in
     match uu____1851 with
     | FStar_Pervasives_Native.None  -> List [String s]
     | FStar_Pervasives_Native.Some l ->
         let uu____1863 =
           FStar_List.map (fun _0_36  -> String _0_36) (s :: l) in
         List uu____1863)
let add_verify_module: Prims.string -> Prims.unit =
  fun s  ->
    let uu____1870 = cons_verify_module s in
    set_option "verify_module" uu____1870
let rec specs: Prims.unit -> FStar_Getopt.opt Prims.list =
  fun uu____1883  ->
    let specs1 =
      [(FStar_Getopt.noshort, "admit_smt_queries",
         (FStar_Getopt.OneArg
            (((fun s  ->
                 if s = "true"
                 then mk_bool true
                 else
                   if s = "false"
                   then mk_bool false
                   else failwith "Invalid argument to --admit_smt_queries")),
              "[true|false]")),
         "Admit SMT queries, unsafe! (default 'false')");
      (FStar_Getopt.noshort, "admit_except",
        (FStar_Getopt.OneArg (mk_string, "[id]")),
        "Admit all verification conditions, except those with query label <id> (eg, --admit_except '(FStar.Fin.pigeonhole, 1)'");
      (FStar_Getopt.noshort, "codegen",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1948 = parse_codegen s in mk_string uu____1948)),
             "[OCaml|FSharp|Kremlin]")), "Generate code for execution");
      (FStar_Getopt.noshort, "codegen-lib",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1966 =
                  let uu____1969 =
                    let uu____1972 = get_codegen_lib () in s :: uu____1972 in
                  FStar_All.pipe_right uu____1969 (FStar_List.map mk_string) in
                List uu____1966)), "[namespace]")),
        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)");
      (FStar_Getopt.noshort, "debug",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1996 =
                  let uu____1999 =
                    let uu____2002 = get_debug () in x :: uu____2002 in
                  FStar_All.pipe_right uu____1999 (FStar_List.map mk_string) in
                List uu____1996)), "[module name]")),
        "Print lots of debugging information while checking module");
      (FStar_Getopt.noshort, "debug_level",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2026 =
                  let uu____2029 =
                    let uu____2032 = get_debug_level () in x :: uu____2032 in
                  FStar_All.pipe_right uu____2029 (FStar_List.map mk_string) in
                List uu____2026)), "[Low|Medium|High|Extreme|...]")),
        "Control the verbosity of debugging info");
      (FStar_Getopt.noshort, "dep",
        (FStar_Getopt.OneArg
           (((fun x  ->
                if (x = "make") || (x = "graph")
                then mk_string x
                else failwith "invalid argument to 'dep'")), "[make|graph]")),
        "Output the transitive closure of the dependency graph in a format suitable for the given tool");
      (FStar_Getopt.noshort, "detail_errors",
        (FStar_Getopt.ZeroArgs ((fun uu____2069  -> mk_bool true))),
        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1");
      (FStar_Getopt.noshort, "detail_hint_replay",
        (FStar_Getopt.ZeroArgs ((fun uu____2083  -> mk_bool true))),
        "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1");
      (FStar_Getopt.noshort, "doc",
        (FStar_Getopt.ZeroArgs ((fun uu____2097  -> mk_bool true))),
        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.");
      (FStar_Getopt.noshort, "dump_module",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2115 =
                  let uu____2118 =
                    let uu____2121 = get_dump_module () in x :: uu____2121 in
                  FStar_All.pipe_right uu____2118 (FStar_List.map mk_string) in
                FStar_All.pipe_right uu____2115 mk_list)), "[module name]")),
        "");
      (FStar_Getopt.noshort, "eager_inference",
        (FStar_Getopt.ZeroArgs ((fun uu____2143  -> mk_bool true))),
        "Solve all type-inference constraints eagerly; more efficient but at the cost of generality");
      (FStar_Getopt.noshort, "explicit_deps",
        (FStar_Getopt.ZeroArgs ((fun uu____2157  -> mk_bool true))),
        "Do not find dependencies automatically, the user provides them on the command-line");
      (FStar_Getopt.noshort, "extract_all",
        (FStar_Getopt.ZeroArgs ((fun uu____2171  -> mk_bool true))),
        "Discover the complete dependency graph and do not stop at interface boundaries");
      (FStar_Getopt.noshort, "extract_module",
        (FStar_Getopt.OneArg (cons_extract_module, "[module name]")),
        "Only extract the specified modules (instead of the possibly-partial dependency graph)");
      (FStar_Getopt.noshort, "extract_namespace",
        (FStar_Getopt.OneArg (cons_extract_namespace, "[namespace name]")),
        "Only extract modules in the specified namespace");
      (FStar_Getopt.noshort, "fstar_home",
        (FStar_Getopt.OneArg (mk_path, "[dir]")),
        "Set the FSTAR_HOME variable to [dir]");
      (FStar_Getopt.noshort, "hide_genident_nums",
        (FStar_Getopt.ZeroArgs ((fun uu____2227  -> mk_bool true))),
        "Don't print generated identifier numbers");
      (FStar_Getopt.noshort, "hide_uvar_nums",
        (FStar_Getopt.ZeroArgs ((fun uu____2241  -> mk_bool true))),
        "Don't print unification variable numbers");
      (FStar_Getopt.noshort, "hint_info",
        (FStar_Getopt.ZeroArgs ((fun uu____2255  -> mk_bool true))),
        "Print information regarding hints");
      (FStar_Getopt.noshort, "hint_file",
        (FStar_Getopt.OneArg (mk_path, "[path]")),
        "Read/write hints to <path> (instead of module-specific hints files)");
      (FStar_Getopt.noshort, "in",
        (FStar_Getopt.ZeroArgs ((fun uu____2283  -> mk_bool true))),
        "Legacy interactive mode; reads input from stdin");
      (FStar_Getopt.noshort, "ide",
        (FStar_Getopt.ZeroArgs ((fun uu____2297  -> mk_bool true))),
        "JSON-based interactive mode for IDEs");
      (FStar_Getopt.noshort, "include",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____2315 =
                  let uu____2318 =
                    let uu____2321 = get_include () in
                    FStar_List.map mk_string uu____2321 in
                  let uu____2324 = let uu____2327 = mk_path s in [uu____2327] in
                  FStar_List.append uu____2318 uu____2324 in
                mk_list uu____2315)), "[path]")),
        "A directory in which to search for files included on the command line");
      (FStar_Getopt.noshort, "indent",
        (FStar_Getopt.ZeroArgs ((fun uu____2341  -> mk_bool true))),
        "Parses and outputs the files on the command line");
      (FStar_Getopt.noshort, "initial_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2359 = FStar_Util.int_of_string x in
                mk_int uu____2359)), "[non-negative integer]")),
        "Number of unrolling of recursive functions to try initially (default 2)");
      (FStar_Getopt.noshort, "initial_ifuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2377 = FStar_Util.int_of_string x in
                mk_int uu____2377)), "[non-negative integer]")),
        "Number of unrolling of inductive datatypes to try at first (default 1)");
      (FStar_Getopt.noshort, "inline_arith",
        (FStar_Getopt.ZeroArgs ((fun uu____2391  -> mk_bool true))),
        "Inline definitions of arithmetic functions in the SMT encoding");
      (FStar_Getopt.noshort, "lax",
        (FStar_Getopt.ZeroArgs ((fun uu____2405  -> mk_bool true))),
        "Run the lax-type checker only (admit all verification conditions)");
      (FStar_Getopt.noshort, "load",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____2423 =
                  let uu____2426 =
                    let uu____2429 = get_load () in
                    FStar_List.map mk_string uu____2429 in
                  let uu____2432 = let uu____2435 = mk_path s in [uu____2435] in
                  FStar_List.append uu____2426 uu____2432 in
                mk_list uu____2423)), "[module]")), "Load compiled module");
      (FStar_Getopt.noshort, "log_types",
        (FStar_Getopt.ZeroArgs ((fun uu____2449  -> mk_bool true))),
        "Print types computed for data/val/let-bindings");
      (FStar_Getopt.noshort, "log_queries",
        (FStar_Getopt.ZeroArgs ((fun uu____2463  -> mk_bool true))),
        "Log the Z3 queries in several queries-*.smt2 files, as we go");
      (FStar_Getopt.noshort, "max_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2481 = FStar_Util.int_of_string x in
                mk_int uu____2481)), "[non-negative integer]")),
        "Number of unrolling of recursive functions to try at most (default 8)");
      (FStar_Getopt.noshort, "max_ifuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2499 = FStar_Util.int_of_string x in
                mk_int uu____2499)), "[non-negative integer]")),
        "Number of unrolling of inductive datatypes to try at most (default 2)");
      (FStar_Getopt.noshort, "min_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2517 = FStar_Util.int_of_string x in
                mk_int uu____2517)), "[non-negative integer]")),
        "Minimum number of unrolling of recursive functions to try (default 1)");
      (FStar_Getopt.noshort, "MLish",
        (FStar_Getopt.ZeroArgs ((fun uu____2531  -> mk_bool true))),
        "Trigger various specializations for compiling the F* compiler itself (not meant for user code)");
      (FStar_Getopt.noshort, "n_cores",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2549 = FStar_Util.int_of_string x in
                mk_int uu____2549)), "[positive integer]")),
        "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)");
      (FStar_Getopt.noshort, "no_default_includes",
        (FStar_Getopt.ZeroArgs ((fun uu____2563  -> mk_bool true))),
        "Ignore the default module search paths");
      (FStar_Getopt.noshort, "no_extract",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2581 =
                  let uu____2584 =
                    let uu____2587 = get_no_extract () in x :: uu____2587 in
                  FStar_All.pipe_right uu____2584 (FStar_List.map mk_string) in
                mk_list uu____2581)), "[module name]")),
        "Do not extract code from this module");
      (FStar_Getopt.noshort, "no_location_info",
        (FStar_Getopt.ZeroArgs ((fun uu____2607  -> mk_bool true))),
        "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)");
      (FStar_Getopt.noshort, "odir",
        (FStar_Getopt.OneArg
           (((fun p  -> let uu____2625 = validate_dir p in mk_path uu____2625)),
             "[dir]")), "Place output in directory [dir]");
      (FStar_Getopt.noshort, "prims",
        (FStar_Getopt.OneArg (mk_string, "file")), "");
      (FStar_Getopt.noshort, "print_bound_var_types",
        (FStar_Getopt.ZeroArgs ((fun uu____2653  -> mk_bool true))),
        "Print the types of bound variables");
      (FStar_Getopt.noshort, "print_effect_args",
        (FStar_Getopt.ZeroArgs ((fun uu____2667  -> mk_bool true))),
        "Print inferred predicate transformers for all computation types");
      (FStar_Getopt.noshort, "print_full_names",
        (FStar_Getopt.ZeroArgs ((fun uu____2681  -> mk_bool true))),
        "Print full names of variables");
      (FStar_Getopt.noshort, "print_implicits",
        (FStar_Getopt.ZeroArgs ((fun uu____2695  -> mk_bool true))),
        "Print implicit arguments");
      (FStar_Getopt.noshort, "print_universes",
        (FStar_Getopt.ZeroArgs ((fun uu____2709  -> mk_bool true))),
        "Print universes");
      (FStar_Getopt.noshort, "print_z3_statistics",
        (FStar_Getopt.ZeroArgs ((fun uu____2723  -> mk_bool true))),
        "Print Z3 statistics for each SMT query");
      (FStar_Getopt.noshort, "prn",
        (FStar_Getopt.ZeroArgs ((fun uu____2737  -> mk_bool true))),
        "Print full names (deprecated; use --print_full_names instead)");
      (FStar_Getopt.noshort, "record_hints",
        (FStar_Getopt.ZeroArgs ((fun uu____2751  -> mk_bool true))),
        "Record a database of hints for efficient proof replay");
      (FStar_Getopt.noshort, "reuse_hint_for",
        (FStar_Getopt.OneArg
           (mk_string, "top-level name in the current module")),
        "Optimistically, attempt using the recorded hint for 'f' when trying to verify some other term 'g'");
      (FStar_Getopt.noshort, "show_signatures",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____2783 =
                  let uu____2786 =
                    let uu____2789 = get_show_signatures () in x ::
                      uu____2789 in
                  FStar_All.pipe_right uu____2786 (FStar_List.map mk_string) in
                mk_list uu____2783)), "[module name]")),
        "Show the checked signatures for all top-level symbols in the module");
      (FStar_Getopt.noshort, "silent",
        (FStar_Getopt.ZeroArgs ((fun uu____2809  -> mk_bool true))), " ");
      (FStar_Getopt.noshort, "smt",
        (FStar_Getopt.OneArg (mk_path, "[path]")),
        "Path to the Z3 SMT solver (we could eventually support other solvers)");
      (FStar_Getopt.noshort, "smtencoding.elim_box",
        (FStar_Getopt.OneArg
           ((string_as_bool "smtencoding.elim_box"), "true|false")),
        "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')");
      (FStar_Getopt.noshort, "smtencoding.nl_arith_repr",
        (FStar_Getopt.OneArg (mk_string, "native|wrapped|boxwrap")),
        "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')");
      (FStar_Getopt.noshort, "smtencoding.l_arith_repr",
        (FStar_Getopt.OneArg (mk_string, "native|boxwrap")),
        "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')");
      (FStar_Getopt.noshort, "split_cases",
        (FStar_Getopt.OneArg
           (((fun n1  ->
                let uu____2883 = FStar_Util.int_of_string n1 in
                mk_int uu____2883)), "[positive integer]")),
        "Partition VC of a match into groups of [n] cases");
      (FStar_Getopt.noshort, "timing",
        (FStar_Getopt.ZeroArgs ((fun uu____2897  -> mk_bool true))),
        "Print the time it takes to verify each top-level definition");
      (FStar_Getopt.noshort, "trace_error",
        (FStar_Getopt.ZeroArgs ((fun uu____2911  -> mk_bool true))),
        "Don't print an error message; show an exception trace instead");
      (FStar_Getopt.noshort, "ugly",
        (FStar_Getopt.ZeroArgs ((fun uu____2925  -> mk_bool true))),
        "Emit output formatted for debugging");
      (FStar_Getopt.noshort, "unthrottle_inductives",
        (FStar_Getopt.ZeroArgs ((fun uu____2939  -> mk_bool true))),
        "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)");
      (FStar_Getopt.noshort, "use_eq_at_higher_order",
        (FStar_Getopt.ZeroArgs ((fun uu____2953  -> mk_bool true))),
        "Use equality constraints when comparing higher-order types (Temporary)");
      (FStar_Getopt.noshort, "use_hints",
        (FStar_Getopt.ZeroArgs ((fun uu____2967  -> mk_bool true))),
        "Use a previously recorded hints database for proof replay");
      (FStar_Getopt.noshort, "no_tactics",
        (FStar_Getopt.ZeroArgs ((fun uu____2981  -> mk_bool true))),
        "Do not run the tactic engine before discharging a VC");
      (FStar_Getopt.noshort, "using_facts_from",
        (FStar_Getopt.OneArg (cons_using_facts_from, "[namespace | fact id]")),
        "Implies --z3refresh; prunes the context to include facts from the given namespace of fact id (multiple uses of this option will prune the context to include those facts that match any of the provided namespaces / fact ids");
      (FStar_Getopt.noshort, "verify_all",
        (FStar_Getopt.ZeroArgs ((fun uu____3009  -> mk_bool true))),
        "With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.");
      (FStar_Getopt.noshort, "verify_module",
        (FStar_Getopt.OneArg (cons_verify_module, "[module name]")),
        "Name of the module to verify");
      (FStar_Getopt.noshort, "__temp_no_proj",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____3041 =
                  let uu____3044 =
                    let uu____3047 = get___temp_no_proj () in x :: uu____3047 in
                  FStar_All.pipe_right uu____3044 (FStar_List.map mk_string) in
                mk_list uu____3041)), "[module name]")),
        "Don't generate projectors for this module");
      ('v', "version",
        (FStar_Getopt.ZeroArgs
           ((fun uu____3068  ->
               display_version (); FStar_All.exit (Prims.parse_int "0")))),
        "Display version number");
      (FStar_Getopt.noshort, "warn_default_effects",
        (FStar_Getopt.ZeroArgs ((fun uu____3083  -> mk_bool true))),
        "Warn when (a -> b) is desugared to (a -> Tot b)");
      (FStar_Getopt.noshort, "z3cliopt",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____3101 =
                  let uu____3104 =
                    let uu____3107 = get_z3cliopt () in
                    FStar_List.append uu____3107 [s] in
                  FStar_All.pipe_right uu____3104 (FStar_List.map mk_string) in
                mk_list uu____3101)), "[option]")),
        "Z3 command line options");
      (FStar_Getopt.noshort, "z3refresh",
        (FStar_Getopt.ZeroArgs ((fun uu____3127  -> mk_bool true))),
        "Restart Z3 after each query; useful for ensuring proof robustness");
      (FStar_Getopt.noshort, "z3rlimit",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____3145 = FStar_Util.int_of_string s in
                mk_int uu____3145)), "[positive integer]")),
        "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)");
      (FStar_Getopt.noshort, "z3rlimit_factor",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____3163 = FStar_Util.int_of_string s in
                mk_int uu____3163)), "[positive integer]")),
        "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)");
      (FStar_Getopt.noshort, "z3seed",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____3181 = FStar_Util.int_of_string s in
                mk_int uu____3181)), "[positive integer]")),
        "Set the Z3 random seed (default 0)");
      (FStar_Getopt.noshort, "__no_positivity",
        (FStar_Getopt.ZeroArgs ((fun uu____3195  -> mk_bool true))),
        "Don't check positivity of inductive types");
      (FStar_Getopt.noshort, "__ml_no_eta_expand_coertions",
        (FStar_Getopt.ZeroArgs ((fun uu____3209  -> mk_bool true))),
        "Do not eta-expand coertions in generated OCaml")] in
    let uu____3220 = FStar_List.map mk_spec specs1 in
    ('h', "help",
      (FStar_Getopt.ZeroArgs
         (fun x  ->
            display_usage_aux specs1; FStar_All.exit (Prims.parse_int "0"))),
      "Display this information") :: uu____3220
and parse_codegen: Prims.string -> Prims.string =
  fun s  ->
    match s with
    | "Kremlin" -> s
    | "OCaml" -> s
    | "FSharp" -> s
    | uu____3260 ->
        (FStar_Util.print_string "Wrong argument to codegen flag\n";
         (let uu____3263 = specs () in display_usage_aux uu____3263);
         FStar_All.exit (Prims.parse_int "1"))
and string_as_bool: Prims.string -> Prims.string -> option_val =
  fun option_name  ->
    fun uu___55_3277  ->
      match uu___55_3277 with
      | "true" -> mk_bool true
      | "false" -> mk_bool false
      | uu____3278 ->
          (FStar_Util.print1 "Wrong argument to %s\n" option_name;
           (let uu____3281 = specs () in display_usage_aux uu____3281);
           FStar_All.exit (Prims.parse_int "1"))
and validate_dir: Prims.string -> Prims.string =
  fun p  -> FStar_Util.mkdir false p; p
let docs:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____3305  ->
    let uu____3306 = specs () in
    FStar_List.map
      (fun uu____3338  ->
         match uu____3338 with
         | (uu____3353,name,uu____3355,doc) -> (name, doc)) uu____3306
let settable: Prims.string -> Prims.bool =
  fun uu___56_3364  ->
    match uu___56_3364 with
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
    | "inline_arith" -> true
    | "lax" -> true
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
    | "using_facts_from" -> true
    | "__temp_no_proj" -> true
    | "reuse_hint_for" -> true
    | "z3rlimit_factor" -> true
    | "z3rlimit" -> true
    | "z3refresh" -> true
    | uu____3365 -> false
let resettable: Prims.string -> Prims.bool =
  fun s  -> ((settable s) || (s = "z3seed")) || (s = "z3cliopt")
let all_specs: FStar_Getopt.opt Prims.list = specs ()
let settable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____3413  ->
          match uu____3413 with
          | (uu____3424,x,uu____3426,uu____3427) -> settable x))
let resettable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____3473  ->
          match uu____3473 with
          | (uu____3484,x,uu____3486,uu____3487) -> resettable x))
let display_usage: Prims.unit -> Prims.unit =
  fun uu____3495  ->
    let uu____3496 = specs () in display_usage_aux uu____3496
let fstar_home: Prims.unit -> Prims.string =
  fun uu____3512  ->
    let uu____3513 = get_fstar_home () in
    match uu____3513 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        ((let uu____3519 =
            let uu____3524 = mk_string x1 in ("fstar_home", uu____3524) in
          set_option' uu____3519);
         x1)
    | FStar_Pervasives_Native.Some x -> x
exception File_argument of Prims.string
let uu___is_File_argument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____3533 -> true
    | uu____3534 -> false
let __proj__File_argument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____3542 -> uu____3542
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
          let uu____3588 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____3588
let file_list_: Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let parse_cmd_line:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____3611  ->
    let res =
      let uu____3613 = specs () in
      FStar_Getopt.parse_cmdline uu____3613
        (fun i  ->
           let uu____3619 =
             let uu____3622 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____3622 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____3619) in
    let uu____3661 =
      let uu____3664 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____3664 in
    (res, uu____3661)
let file_list: Prims.unit -> Prims.string Prims.list =
  fun uu____3692  -> FStar_ST.op_Bang file_list_
let restore_cmd_line_options: Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____3721 = specs () in
       FStar_Getopt.parse_cmdline uu____3721 (fun x  -> ()) in
     (let uu____3727 =
        let uu____3732 =
          let uu____3733 = FStar_List.map mk_string old_verify_module in
          List uu____3733 in
        ("verify_module", uu____3732) in
      set_option' uu____3727);
     r)
let should_verify: Prims.string -> Prims.bool =
  fun m  ->
    let uu____3740 = get_lax () in
    if uu____3740
    then false
    else
      (let uu____3742 = get_verify_all () in
       if uu____3742
       then true
       else
         (let uu____3744 = get_verify_module () in
          match uu____3744 with
          | [] ->
              let uu____3747 = file_list () in
              FStar_List.existsML
                (fun f  ->
                   let f1 = FStar_Util.basename f in
                   let f2 =
                     let uu____3756 =
                       let uu____3757 =
                         let uu____3758 =
                           let uu____3759 = FStar_Util.get_file_extension f1 in
                           FStar_String.length uu____3759 in
                         (FStar_String.length f1) - uu____3758 in
                       uu____3757 - (Prims.parse_int "1") in
                     FStar_String.substring f1 (Prims.parse_int "0")
                       uu____3756 in
                   (FStar_String.lowercase f2) = m) uu____3747
          | l -> FStar_List.contains (FStar_String.lowercase m) l))
let dont_gen_projectors: Prims.string -> Prims.bool =
  fun m  ->
    let uu____3767 = get___temp_no_proj () in
    FStar_List.contains m uu____3767
let should_print_message: Prims.string -> Prims.bool =
  fun m  ->
    let uu____3774 = should_verify m in
    if uu____3774 then m <> "Prims" else false
let include_path: Prims.unit -> Prims.string Prims.list =
  fun uu____3781  ->
    let uu____3782 = get_no_default_includes () in
    if uu____3782
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____3790 =
         let uu____3793 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____3793
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____3806 =
         let uu____3809 = get_include () in
         FStar_List.append uu____3809 ["."] in
       FStar_List.append uu____3790 uu____3806)
let find_file: Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____3818 = FStar_Util.is_path_absolute filename in
    if uu____3818
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____3825 =
         let uu____3828 = include_path () in FStar_List.rev uu____3828 in
       FStar_Util.find_map uu____3825
         (fun p  ->
            let path = FStar_Util.join_paths p filename in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
let prims: Prims.unit -> Prims.string =
  fun uu____3841  ->
    let uu____3842 = get_prims () in
    match uu____3842 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst" in
        let uu____3846 = find_file filename in
        (match uu____3846 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____3850 =
               let uu____3851 =
                 FStar_Util.format1
                   "unable to find required file \"%s\" in the module search path.\n"
                   filename in
               FStar_Util.Failure uu____3851 in
             FStar_Exn.raise uu____3850)
    | FStar_Pervasives_Native.Some x -> x
let prims_basename: Prims.unit -> Prims.string =
  fun uu____3856  ->
    let uu____3857 = prims () in FStar_Util.basename uu____3857
let pervasives: Prims.unit -> Prims.string =
  fun uu____3861  ->
    let filename = "FStar.Pervasives.fst" in
    let uu____3863 = find_file filename in
    match uu____3863 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____3867 =
          let uu____3868 =
            FStar_Util.format1
              "unable to find required file \"%s\" in the module search path.\n"
              filename in
          FStar_Util.Failure uu____3868 in
        FStar_Exn.raise uu____3867
let pervasives_basename: Prims.unit -> Prims.string =
  fun uu____3872  ->
    let uu____3873 = pervasives () in FStar_Util.basename uu____3873
let pervasives_native_basename: Prims.unit -> Prims.string =
  fun uu____3877  ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____3879 = find_file filename in
    match uu____3879 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____3883 =
          let uu____3884 =
            FStar_Util.format1
              "unable to find required file \"%s\" in the module search path.\n"
              filename in
          FStar_Util.Failure uu____3884 in
        FStar_Exn.raise uu____3883
let prepend_output_dir: Prims.string -> Prims.string =
  fun fname  ->
    let uu____3889 = get_odir () in
    match uu____3889 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
let __temp_no_proj: Prims.string -> Prims.bool =
  fun s  ->
    let uu____3897 = get___temp_no_proj () in
    FStar_All.pipe_right uu____3897 (FStar_List.contains s)
let admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____3905  -> get_admit_smt_queries ()
let admit_except: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____3911  -> get_admit_except ()
let codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____3917  -> get_codegen ()
let codegen_libs: Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____3925  ->
    let uu____3926 = get_codegen_lib () in
    FStar_All.pipe_right uu____3926
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
let debug_any: Prims.unit -> Prims.bool =
  fun uu____3942  -> let uu____3943 = get_debug () in uu____3943 <> []
let debug_at_level: Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      (let uu____3958 = get_debug () in
       FStar_All.pipe_right uu____3958 (FStar_List.contains modul)) &&
        (debug_level_geq level)
let dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____3968  -> get_dep ()
let detail_errors: Prims.unit -> Prims.bool =
  fun uu____3972  -> get_detail_errors ()
let detail_hint_replay: Prims.unit -> Prims.bool =
  fun uu____3976  -> get_detail_hint_replay ()
let doc: Prims.unit -> Prims.bool = fun uu____3980  -> get_doc ()
let dump_module: Prims.string -> Prims.bool =
  fun s  ->
    let uu____3985 = get_dump_module () in
    FStar_All.pipe_right uu____3985 (FStar_List.contains s)
let eager_inference: Prims.unit -> Prims.bool =
  fun uu____3993  -> get_eager_inference ()
let explicit_deps: Prims.unit -> Prims.bool =
  fun uu____3997  -> get_explicit_deps ()
let extract_all: Prims.unit -> Prims.bool =
  fun uu____4001  -> get_extract_all ()
let fs_typ_app: Prims.string -> Prims.bool =
  fun filename  ->
    let uu____4006 = FStar_ST.op_Bang light_off_files in
    FStar_List.contains filename uu____4006
let full_context_dependency: Prims.unit -> Prims.bool =
  fun uu____4030  -> true
let hide_genident_nums: Prims.unit -> Prims.bool =
  fun uu____4034  -> get_hide_genident_nums ()
let hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____4038  -> get_hide_uvar_nums ()
let hint_info: Prims.unit -> Prims.bool = fun uu____4042  -> get_hint_info ()
let hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____4048  -> get_hint_file ()
let ide: Prims.unit -> Prims.bool = fun uu____4052  -> get_ide ()
let indent: Prims.unit -> Prims.bool = fun uu____4056  -> get_indent ()
let initial_fuel: Prims.unit -> Prims.int =
  fun uu____4060  ->
    let uu____4061 = get_initial_fuel () in
    let uu____4062 = get_max_fuel () in Prims.min uu____4061 uu____4062
let initial_ifuel: Prims.unit -> Prims.int =
  fun uu____4066  ->
    let uu____4067 = get_initial_ifuel () in
    let uu____4068 = get_max_ifuel () in Prims.min uu____4067 uu____4068
let interactive: Prims.unit -> Prims.bool =
  fun uu____4072  -> (get_in ()) || (get_ide ())
let lax: Prims.unit -> Prims.bool = fun uu____4076  -> get_lax ()
let load: Prims.unit -> Prims.string Prims.list =
  fun uu____4082  -> get_load ()
let legacy_interactive: Prims.unit -> Prims.bool =
  fun uu____4086  -> get_in ()
let log_queries: Prims.unit -> Prims.bool =
  fun uu____4090  -> get_log_queries ()
let log_types: Prims.unit -> Prims.bool = fun uu____4094  -> get_log_types ()
let max_fuel: Prims.unit -> Prims.int = fun uu____4098  -> get_max_fuel ()
let max_ifuel: Prims.unit -> Prims.int = fun uu____4102  -> get_max_ifuel ()
let min_fuel: Prims.unit -> Prims.int = fun uu____4106  -> get_min_fuel ()
let ml_ish: Prims.unit -> Prims.bool = fun uu____4110  -> get_MLish ()
let set_ml_ish: Prims.unit -> Prims.unit =
  fun uu____4114  -> set_option "MLish" (Bool true)
let n_cores: Prims.unit -> Prims.int = fun uu____4118  -> get_n_cores ()
let no_default_includes: Prims.unit -> Prims.bool =
  fun uu____4122  -> get_no_default_includes ()
let no_extract: Prims.string -> Prims.bool =
  fun s  ->
    let uu____4127 = get_no_extract () in
    FStar_All.pipe_right uu____4127 (FStar_List.contains s)
let no_location_info: Prims.unit -> Prims.bool =
  fun uu____4135  -> get_no_location_info ()
let output_dir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____4141  -> get_odir ()
let ugly: Prims.unit -> Prims.bool = fun uu____4145  -> get_ugly ()
let print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____4149  -> get_print_bound_var_types ()
let print_effect_args: Prims.unit -> Prims.bool =
  fun uu____4153  -> get_print_effect_args ()
let print_implicits: Prims.unit -> Prims.bool =
  fun uu____4157  -> get_print_implicits ()
let print_real_names: Prims.unit -> Prims.bool =
  fun uu____4161  -> (get_prn ()) || (get_print_full_names ())
let print_universes: Prims.unit -> Prims.bool =
  fun uu____4165  -> get_print_universes ()
let print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____4169  -> get_print_z3_statistics ()
let record_hints: Prims.unit -> Prims.bool =
  fun uu____4173  -> get_record_hints ()
let reuse_hint_for: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____4179  -> get_reuse_hint_for ()
let silent: Prims.unit -> Prims.bool = fun uu____4183  -> get_silent ()
let smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____4187  -> get_smtencoding_elim_box ()
let smtencoding_nl_arith_native: Prims.unit -> Prims.bool =
  fun uu____4191  ->
    let uu____4192 = get_smtencoding_nl_arith_repr () in
    uu____4192 = "native"
let smtencoding_nl_arith_wrapped: Prims.unit -> Prims.bool =
  fun uu____4196  ->
    let uu____4197 = get_smtencoding_nl_arith_repr () in
    uu____4197 = "wrapped"
let smtencoding_nl_arith_default: Prims.unit -> Prims.bool =
  fun uu____4201  ->
    let uu____4202 = get_smtencoding_nl_arith_repr () in
    uu____4202 = "boxwrap"
let smtencoding_l_arith_native: Prims.unit -> Prims.bool =
  fun uu____4206  ->
    let uu____4207 = get_smtencoding_l_arith_repr () in uu____4207 = "native"
let smtencoding_l_arith_default: Prims.unit -> Prims.bool =
  fun uu____4211  ->
    let uu____4212 = get_smtencoding_l_arith_repr () in
    uu____4212 = "boxwrap"
let split_cases: Prims.unit -> Prims.int =
  fun uu____4216  -> get_split_cases ()
let timing: Prims.unit -> Prims.bool = fun uu____4220  -> get_timing ()
let trace_error: Prims.unit -> Prims.bool =
  fun uu____4224  -> get_trace_error ()
let unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____4228  -> get_unthrottle_inductives ()
let use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____4232  -> get_use_eq_at_higher_order ()
let use_hints: Prims.unit -> Prims.bool = fun uu____4236  -> get_use_hints ()
let use_tactics: Prims.unit -> Prims.bool =
  fun uu____4240  -> get_use_tactics ()
let using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____4248  -> get_using_facts_from ()
let verify_all: Prims.unit -> Prims.bool =
  fun uu____4252  -> get_verify_all ()
let verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____4258  -> get_verify_module ()
let warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____4262  -> get_warn_default_effects ()
let z3_exe: Prims.unit -> Prims.string =
  fun uu____4266  ->
    let uu____4267 = get_smt () in
    match uu____4267 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let z3_cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____4276  -> get_z3cliopt ()
let z3_refresh: Prims.unit -> Prims.bool =
  fun uu____4280  -> get_z3refresh ()
let z3_rlimit: Prims.unit -> Prims.int = fun uu____4284  -> get_z3rlimit ()
let z3_rlimit_factor: Prims.unit -> Prims.int =
  fun uu____4288  -> get_z3rlimit_factor ()
let z3_seed: Prims.unit -> Prims.int = fun uu____4292  -> get_z3seed ()
let no_positivity: Prims.unit -> Prims.bool =
  fun uu____4296  -> get_no_positivity ()
let ml_no_eta_expand_coertions: Prims.unit -> Prims.bool =
  fun uu____4300  -> get_ml_no_eta_expand_coertions ()
let should_extract: Prims.string -> Prims.bool =
  fun m  ->
    (let uu____4307 = no_extract m in Prims.op_Negation uu____4307) &&
      ((extract_all ()) ||
         (let uu____4310 = get_extract_module () in
          match uu____4310 with
          | [] ->
              let uu____4313 = get_extract_namespace () in
              (match uu____4313 with
               | [] -> true
               | ns ->
                   FStar_Util.for_some
                     (FStar_Util.starts_with (FStar_String.lowercase m)) ns)
          | l -> FStar_List.contains (FStar_String.lowercase m) l))