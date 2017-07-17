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
    match projectee with | Bool _0 -> true | uu____65 -> false
let __proj__Bool__item___0: option_val -> Prims.bool =
  fun projectee  -> match projectee with | Bool _0 -> _0
let uu___is_String: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____79 -> false
let __proj__String__item___0: option_val -> Prims.string =
  fun projectee  -> match projectee with | String _0 -> _0
let uu___is_Path: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____93 -> false
let __proj__Path__item___0: option_val -> Prims.string =
  fun projectee  -> match projectee with | Path _0 -> _0
let uu___is_Int: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____107 -> false
let __proj__Int__item___0: option_val -> Prims.int =
  fun projectee  -> match projectee with | Int _0 -> _0
let uu___is_List: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____122 -> false
let __proj__List__item___0: option_val -> option_val Prims.list =
  fun projectee  -> match projectee with | List _0 -> _0
let uu___is_Unset: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____138 -> false
type options =
  | Set
  | Reset
  | Restore
let uu___is_Set: options -> Prims.bool =
  fun projectee  -> match projectee with | Set  -> true | uu____143 -> false
let uu___is_Reset: options -> Prims.bool =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____148 -> false
let uu___is_Restore: options -> Prims.bool =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____153 -> false
let __unit_tests__: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let __unit_tests: Prims.unit -> Prims.bool =
  fun uu____160  -> FStar_ST.read __unit_tests__
let __set_unit_tests: Prims.unit -> Prims.unit =
  fun uu____166  -> FStar_ST.write __unit_tests__ true
let __clear_unit_tests: Prims.unit -> Prims.unit =
  fun uu____172  -> FStar_ST.write __unit_tests__ false
let as_bool: option_val -> Prims.bool =
  fun uu___49_178  ->
    match uu___49_178 with
    | Bool b -> b
    | uu____180 -> failwith "Impos: expected Bool"
let as_int: option_val -> Prims.int =
  fun uu___50_184  ->
    match uu___50_184 with
    | Int b -> b
    | uu____186 -> failwith "Impos: expected Int"
let as_string: option_val -> Prims.string =
  fun uu___51_190  ->
    match uu___51_190 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____193 -> failwith "Impos: expected String"
let as_list as_t uu___52_212 =
  match uu___52_212 with
  | List ts -> FStar_All.pipe_right ts (FStar_List.map as_t)
  | uu____219 -> failwith "Impos: expected List"
let as_option as_t uu___53_239 =
  match uu___53_239 with
  | Unset  -> FStar_Pervasives_Native.None
  | v1 -> let uu____243 = as_t v1 in FStar_Pervasives_Native.Some uu____243
type optionstate = option_val FStar_Util.smap
let fstar_options: optionstate Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let peek: Prims.unit -> optionstate =
  fun uu____253  ->
    let uu____254 = FStar_ST.read fstar_options in FStar_List.hd uu____254
let pop: Prims.unit -> Prims.unit =
  fun uu____262  ->
    let uu____263 = FStar_ST.read fstar_options in
    match uu____263 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____268::[] -> failwith "TOO MANY POPS!"
    | uu____269::tl1 -> FStar_ST.write fstar_options tl1
let push: Prims.unit -> Prims.unit =
  fun uu____278  ->
    let uu____279 =
      let uu____281 =
        let uu____283 = peek () in FStar_Util.smap_copy uu____283 in
      let uu____285 = FStar_ST.read fstar_options in uu____281 :: uu____285 in
    FStar_ST.write fstar_options uu____279
let set: optionstate -> Prims.unit =
  fun o  ->
    let uu____299 = FStar_ST.read fstar_options in
    match uu____299 with
    | [] -> failwith "set on empty option stack"
    | uu____304::os -> FStar_ST.write fstar_options (o :: os)
let set_option: Prims.string -> option_val -> Prims.unit =
  fun k  ->
    fun v1  -> let uu____318 = peek () in FStar_Util.smap_add uu____318 k v1
let set_option':
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> Prims.unit =
  fun uu____325  -> match uu____325 with | (k,v1) -> set_option k v1
let with_saved_options f = push (); (let retv = f () in pop (); retv)
let light_off_files: Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let add_light_off_file: Prims.string -> Prims.unit =
  fun filename  ->
    let uu____356 =
      let uu____358 = FStar_ST.read light_off_files in filename :: uu____358 in
    FStar_ST.write light_off_files uu____356
let defaults:
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 Prims.list =
  [("__temp_no_proj", (List []));
  ("_fstar_home", (String ""));
  ("_include_path", (List []));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
  ("check_hints", (Bool false));
  ("codegen", Unset);
  ("codegen-lib", (List []));
  ("debug", (List []));
  ("debug_level", (List []));
  ("dep", Unset);
  ("detail_errors", (Bool false));
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
  ("print_fuels", (Bool false));
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
  ("__no_positivity", (Bool false))]
let init: Prims.unit -> Prims.unit =
  fun uu____540  ->
    let o = peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let clear: Prims.unit -> Prims.unit =
  fun uu____551  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50") in
    FStar_ST.write fstar_options [o];
    FStar_ST.write light_off_files [];
    init ()
let _run: Prims.unit = clear ()
let get_option: Prims.string -> option_val =
  fun s  ->
    let uu____568 =
      let uu____570 = peek () in FStar_Util.smap_try_find uu____570 s in
    match uu____568 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
let lookup_opt s c = c (get_option s)
let get_admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____596  -> lookup_opt "admit_smt_queries" as_bool
let get_admit_except:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____601  -> lookup_opt "admit_except" (as_option as_string)
let get_check_hints: Prims.unit -> Prims.bool =
  fun uu____606  -> lookup_opt "check_hints" as_bool
let get_codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____611  -> lookup_opt "codegen" (as_option as_string)
let get_codegen_lib: Prims.unit -> Prims.string Prims.list =
  fun uu____617  -> lookup_opt "codegen-lib" (as_list as_string)
let get_debug: Prims.unit -> Prims.string Prims.list =
  fun uu____623  -> lookup_opt "debug" (as_list as_string)
let get_debug_level: Prims.unit -> Prims.string Prims.list =
  fun uu____629  -> lookup_opt "debug_level" (as_list as_string)
let get_dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____635  -> lookup_opt "dep" (as_option as_string)
let get_detail_errors: Prims.unit -> Prims.bool =
  fun uu____640  -> lookup_opt "detail_errors" as_bool
let get_doc: Prims.unit -> Prims.bool =
  fun uu____644  -> lookup_opt "doc" as_bool
let get_dump_module: Prims.unit -> Prims.string Prims.list =
  fun uu____649  -> lookup_opt "dump_module" (as_list as_string)
let get_eager_inference: Prims.unit -> Prims.bool =
  fun uu____654  -> lookup_opt "eager_inference" as_bool
let get_explicit_deps: Prims.unit -> Prims.bool =
  fun uu____658  -> lookup_opt "explicit_deps" as_bool
let get_extract_all: Prims.unit -> Prims.bool =
  fun uu____662  -> lookup_opt "extract_all" as_bool
let get_extract_module: Prims.unit -> Prims.string Prims.list =
  fun uu____667  -> lookup_opt "extract_module" (as_list as_string)
let get_extract_namespace: Prims.unit -> Prims.string Prims.list =
  fun uu____673  -> lookup_opt "extract_namespace" (as_list as_string)
let get_fs_typ_app: Prims.unit -> Prims.bool =
  fun uu____678  -> lookup_opt "fs_typ_app" as_bool
let get_fstar_home: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____683  -> lookup_opt "fstar_home" (as_option as_string)
let get_hide_genident_nums: Prims.unit -> Prims.bool =
  fun uu____688  -> lookup_opt "hide_genident_nums" as_bool
let get_hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____692  -> lookup_opt "hide_uvar_nums" as_bool
let get_hint_info: Prims.unit -> Prims.bool =
  fun uu____696  -> lookup_opt "hint_info" as_bool
let get_hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____701  -> lookup_opt "hint_file" (as_option as_string)
let get_in: Prims.unit -> Prims.bool =
  fun uu____706  -> lookup_opt "in" as_bool
let get_ide: Prims.unit -> Prims.bool =
  fun uu____710  -> lookup_opt "ide" as_bool
let get_include: Prims.unit -> Prims.string Prims.list =
  fun uu____715  -> lookup_opt "include" (as_list as_string)
let get_indent: Prims.unit -> Prims.bool =
  fun uu____720  -> lookup_opt "indent" as_bool
let get_initial_fuel: Prims.unit -> Prims.int =
  fun uu____724  -> lookup_opt "initial_fuel" as_int
let get_initial_ifuel: Prims.unit -> Prims.int =
  fun uu____728  -> lookup_opt "initial_ifuel" as_int
let get_lax: Prims.unit -> Prims.bool =
  fun uu____732  -> lookup_opt "lax" as_bool
let get_load: Prims.unit -> Prims.string Prims.list =
  fun uu____737  -> lookup_opt "load" (as_list as_string)
let get_log_queries: Prims.unit -> Prims.bool =
  fun uu____742  -> lookup_opt "log_queries" as_bool
let get_log_types: Prims.unit -> Prims.bool =
  fun uu____746  -> lookup_opt "log_types" as_bool
let get_max_fuel: Prims.unit -> Prims.int =
  fun uu____750  -> lookup_opt "max_fuel" as_int
let get_max_ifuel: Prims.unit -> Prims.int =
  fun uu____754  -> lookup_opt "max_ifuel" as_int
let get_min_fuel: Prims.unit -> Prims.int =
  fun uu____758  -> lookup_opt "min_fuel" as_int
let get_MLish: Prims.unit -> Prims.bool =
  fun uu____762  -> lookup_opt "MLish" as_bool
let get_n_cores: Prims.unit -> Prims.int =
  fun uu____766  -> lookup_opt "n_cores" as_int
let get_no_default_includes: Prims.unit -> Prims.bool =
  fun uu____770  -> lookup_opt "no_default_includes" as_bool
let get_no_extract: Prims.unit -> Prims.string Prims.list =
  fun uu____775  -> lookup_opt "no_extract" (as_list as_string)
let get_no_location_info: Prims.unit -> Prims.bool =
  fun uu____780  -> lookup_opt "no_location_info" as_bool
let get_odir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____785  -> lookup_opt "odir" (as_option as_string)
let get_ugly: Prims.unit -> Prims.bool =
  fun uu____790  -> lookup_opt "ugly" as_bool
let get_prims: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____795  -> lookup_opt "prims" (as_option as_string)
let get_print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____800  -> lookup_opt "print_bound_var_types" as_bool
let get_print_effect_args: Prims.unit -> Prims.bool =
  fun uu____804  -> lookup_opt "print_effect_args" as_bool
let get_print_fuels: Prims.unit -> Prims.bool =
  fun uu____808  -> lookup_opt "print_fuels" as_bool
let get_print_full_names: Prims.unit -> Prims.bool =
  fun uu____812  -> lookup_opt "print_full_names" as_bool
let get_print_implicits: Prims.unit -> Prims.bool =
  fun uu____816  -> lookup_opt "print_implicits" as_bool
let get_print_universes: Prims.unit -> Prims.bool =
  fun uu____820  -> lookup_opt "print_universes" as_bool
let get_print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____824  -> lookup_opt "print_z3_statistics" as_bool
let get_prn: Prims.unit -> Prims.bool =
  fun uu____828  -> lookup_opt "prn" as_bool
let get_record_hints: Prims.unit -> Prims.bool =
  fun uu____832  -> lookup_opt "record_hints" as_bool
let get_reuse_hint_for:
  Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____837  -> lookup_opt "reuse_hint_for" (as_option as_string)
let get_show_signatures: Prims.unit -> Prims.string Prims.list =
  fun uu____843  -> lookup_opt "show_signatures" (as_list as_string)
let get_silent: Prims.unit -> Prims.bool =
  fun uu____848  -> lookup_opt "silent" as_bool
let get_smt: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____853  -> lookup_opt "smt" (as_option as_string)
let get_smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____858  -> lookup_opt "smtencoding.elim_box" as_bool
let get_smtencoding_nl_arith_repr: Prims.unit -> Prims.string =
  fun uu____862  -> lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr: Prims.unit -> Prims.string =
  fun uu____866  -> lookup_opt "smtencoding.l_arith_repr" as_string
let get_split_cases: Prims.unit -> Prims.int =
  fun uu____870  -> lookup_opt "split_cases" as_int
let get_timing: Prims.unit -> Prims.bool =
  fun uu____874  -> lookup_opt "timing" as_bool
let get_trace_error: Prims.unit -> Prims.bool =
  fun uu____878  -> lookup_opt "trace_error" as_bool
let get_unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____882  -> lookup_opt "unthrottle_inductives" as_bool
let get_use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____886  -> lookup_opt "use_eq_at_higher_order" as_bool
let get_use_hints: Prims.unit -> Prims.bool =
  fun uu____890  -> lookup_opt "use_hints" as_bool
let get_use_tactics: Prims.unit -> Prims.bool =
  fun uu____894  ->
    let uu____895 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____895
let get_using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____901  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let get_verify_all: Prims.unit -> Prims.bool =
  fun uu____908  -> lookup_opt "verify_all" as_bool
let get_verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____913  -> lookup_opt "verify_module" (as_list as_string)
let get___temp_no_proj: Prims.unit -> Prims.string Prims.list =
  fun uu____919  -> lookup_opt "__temp_no_proj" (as_list as_string)
let get_version: Prims.unit -> Prims.bool =
  fun uu____924  -> lookup_opt "version" as_bool
let get_warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____928  -> lookup_opt "warn_default_effects" as_bool
let get_z3cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____933  -> lookup_opt "z3cliopt" (as_list as_string)
let get_z3refresh: Prims.unit -> Prims.bool =
  fun uu____938  -> lookup_opt "z3refresh" as_bool
let get_z3rlimit: Prims.unit -> Prims.int =
  fun uu____942  -> lookup_opt "z3rlimit" as_int
let get_z3rlimit_factor: Prims.unit -> Prims.int =
  fun uu____946  -> lookup_opt "z3rlimit_factor" as_int
let get_z3seed: Prims.unit -> Prims.int =
  fun uu____950  -> lookup_opt "z3seed" as_int
let get_no_positivity: Prims.unit -> Prims.bool =
  fun uu____954  -> lookup_opt "__no_positivity" as_bool
let dlevel: Prims.string -> debug_level_t =
  fun uu___54_958  ->
    match uu___54_958 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let one_debug_level_geq: debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____968 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let debug_level_geq: debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____973 = get_debug_level () in
    FStar_All.pipe_right uu____973
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
let universe_include_path_base_dirs: Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"]
let _version: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _platform: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _compiler: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _date: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _commit: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let display_version: Prims.unit -> Prims.unit =
  fun uu____1002  ->
    let uu____1003 =
      let uu____1004 = FStar_ST.read _version in
      let uu____1007 = FStar_ST.read _platform in
      let uu____1010 = FStar_ST.read _compiler in
      let uu____1013 = FStar_ST.read _date in
      let uu____1016 = FStar_ST.read _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1004
        uu____1007 uu____1010 uu____1013 uu____1016 in
    FStar_Util.print_string uu____1003
let display_usage_aux specs =
  FStar_Util.print_string "fstar.exe [options] file[s]\n";
  FStar_List.iter
    (fun uu____1056  ->
       match uu____1056 with
       | (uu____1062,flag,p,doc) ->
           (match p with
            | FStar_Getopt.ZeroArgs ig ->
                if doc = ""
                then
                  let uu____1071 =
                    let uu____1072 = FStar_Util.colorize_bold flag in
                    FStar_Util.format1 "  --%s\n" uu____1072 in
                  FStar_Util.print_string uu____1071
                else
                  (let uu____1074 =
                     let uu____1075 = FStar_Util.colorize_bold flag in
                     FStar_Util.format2 "  --%s  %s\n" uu____1075 doc in
                   FStar_Util.print_string uu____1074)
            | FStar_Getopt.OneArg (uu____1076,argname) ->
                if doc = ""
                then
                  let uu____1082 =
                    let uu____1083 = FStar_Util.colorize_bold flag in
                    let uu____1084 = FStar_Util.colorize_bold argname in
                    FStar_Util.format2 "  --%s %s\n" uu____1083 uu____1084 in
                  FStar_Util.print_string uu____1082
                else
                  (let uu____1086 =
                     let uu____1087 = FStar_Util.colorize_bold flag in
                     let uu____1088 = FStar_Util.colorize_bold argname in
                     FStar_Util.format3 "  --%s %s  %s\n" uu____1087
                       uu____1088 doc in
                   FStar_Util.print_string uu____1086))) specs
let mk_spec:
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____1103 = o in
    match uu____1103 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____1124 =
                let uu____1125 = let uu____1128 = f () in (name, uu____1128) in
                set_option' uu____1125 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x =
                let uu____1139 = let uu____1142 = f x in (name, uu____1142) in
                set_option' uu____1139 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let cons_extract_module: Prims.string -> option_val =
  fun s  ->
    let uu____1150 =
      let uu____1152 =
        let uu____1154 = get_extract_module () in (FStar_String.lowercase s)
          :: uu____1154 in
      FStar_All.pipe_right uu____1152
        (FStar_List.map (fun _0_26  -> String _0_26)) in
    List uu____1150
let cons_extract_namespace: Prims.string -> option_val =
  fun s  ->
    let uu____1162 =
      let uu____1164 =
        let uu____1166 = get_extract_namespace () in
        (FStar_String.lowercase s) :: uu____1166 in
      FStar_All.pipe_right uu____1164
        (FStar_List.map (fun _0_27  -> String _0_27)) in
    List uu____1162
let add_extract_module: Prims.string -> Prims.unit =
  fun s  ->
    let uu____1174 = cons_extract_module s in
    set_option "extract_module" uu____1174
let add_extract_namespace: Prims.string -> Prims.unit =
  fun s  ->
    let uu____1179 = cons_extract_namespace s in
    set_option "extract_namespace" uu____1179
let cons_verify_module: Prims.string -> option_val =
  fun s  ->
    let uu____1184 =
      let uu____1186 =
        let uu____1188 = get_verify_module () in (FStar_String.lowercase s)
          :: uu____1188 in
      FStar_All.pipe_right uu____1186
        (FStar_List.map (fun _0_28  -> String _0_28)) in
    List uu____1184
let cons_using_facts_from: Prims.string -> option_val =
  fun s  ->
    set_option "z3refresh" (Bool true);
    (let uu____1197 = get_using_facts_from () in
     match uu____1197 with
     | FStar_Pervasives_Native.None  -> List [String s]
     | FStar_Pervasives_Native.Some l ->
         let uu____1204 =
           FStar_List.map (fun _0_29  -> String _0_29) (s :: l) in
         List uu____1204)
let add_verify_module: Prims.string -> Prims.unit =
  fun s  ->
    let uu____1210 = cons_verify_module s in
    set_option "verify_module" uu____1210
let rec specs:
  Prims.unit ->
    (FStar_Char.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  fun uu____1222  ->
    let specs1 =
      [(FStar_Getopt.noshort, "admit_smt_queries",
         (FStar_Getopt.OneArg
            (((fun s  ->
                 if s = "true"
                 then Bool true
                 else
                   if s = "false"
                   then Bool false
                   else failwith "Invalid argument to --admit_smt_queries")),
              "[true|false]")),
         "Admit SMT queries, unsafe! (default 'false')");
      (FStar_Getopt.noshort, "admit_except",
        (FStar_Getopt.OneArg (((fun _0_30  -> String _0_30)), "[id]")),
        "Admit all verification conditions, except those with query label <id>");
      (FStar_Getopt.noshort, "codegen",
        (FStar_Getopt.OneArg
           (((fun s  -> let uu____1262 = parse_codegen s in String uu____1262)),
             "[OCaml|FSharp|Kremlin]")), "Generate code for execution");
      (FStar_Getopt.noshort, "codegen-lib",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1274 =
                  let uu____1276 =
                    let uu____1278 = get_codegen_lib () in s :: uu____1278 in
                  FStar_All.pipe_right uu____1276
                    (FStar_List.map (fun _0_31  -> String _0_31)) in
                List uu____1274)), "[namespace]")),
        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)");
      (FStar_Getopt.noshort, "debug",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1293 =
                  let uu____1295 =
                    let uu____1297 = get_debug () in x :: uu____1297 in
                  FStar_All.pipe_right uu____1295
                    (FStar_List.map (fun _0_32  -> String _0_32)) in
                List uu____1293)), "[module name]")),
        "Print lots of debugging information while checking module");
      (FStar_Getopt.noshort, "debug_level",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1312 =
                  let uu____1314 =
                    let uu____1316 = get_debug_level () in x :: uu____1316 in
                  FStar_All.pipe_right uu____1314
                    (FStar_List.map (fun _0_33  -> String _0_33)) in
                List uu____1312)), "[Low|Medium|High|Extreme|...]")),
        "Control the verbosity of debugging info");
      (FStar_Getopt.noshort, "dep",
        (FStar_Getopt.OneArg
           (((fun x  ->
                if (x = "make") || (x = "graph")
                then String x
                else failwith "invalid argument to 'dep'")), "[make|graph]")),
        "Output the transitive closure of the dependency graph in a format suitable for the given tool");
      (FStar_Getopt.noshort, "detail_errors",
        (FStar_Getopt.ZeroArgs ((fun uu____1338  -> Bool true))),
        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1");
      (FStar_Getopt.noshort, "doc",
        (FStar_Getopt.ZeroArgs ((fun uu____1346  -> Bool true))),
        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.");
      (FStar_Getopt.noshort, "dump_module",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1358 =
                  let uu____1360 =
                    let uu____1362 = get_dump_module () in x :: uu____1362 in
                  FStar_All.pipe_right uu____1360
                    (FStar_List.map (fun _0_34  -> String _0_34)) in
                FStar_All.pipe_right uu____1358 (fun _0_35  -> List _0_35))),
             "[module name]")), "");
      (FStar_Getopt.noshort, "eager_inference",
        (FStar_Getopt.ZeroArgs ((fun uu____1374  -> Bool true))),
        "Solve all type-inference constraints eagerly; more efficient but at the cost of generality");
      (FStar_Getopt.noshort, "explicit_deps",
        (FStar_Getopt.ZeroArgs ((fun uu____1382  -> Bool true))),
        "Do not find dependencies automatically, the user provides them on the command-line");
      (FStar_Getopt.noshort, "extract_all",
        (FStar_Getopt.ZeroArgs ((fun uu____1390  -> Bool true))),
        "Discover the complete dependency graph and do not stop at interface boundaries");
      (FStar_Getopt.noshort, "extract_module",
        (FStar_Getopt.OneArg (cons_extract_module, "[module name]")),
        "Only extract the specified modules (instead of the possibly-partial dependency graph)");
      (FStar_Getopt.noshort, "extract_namespace",
        (FStar_Getopt.OneArg (cons_extract_namespace, "[namespace name]")),
        "Only extract modules in the specified namespace");
      (FStar_Getopt.noshort, "fstar_home",
        (FStar_Getopt.OneArg (((fun _0_36  -> Path _0_36)), "[dir]")),
        "Set the FSTAR_HOME variable to [dir]");
      (FStar_Getopt.noshort, "hide_genident_nums",
        (FStar_Getopt.ZeroArgs ((fun uu____1422  -> Bool true))),
        "Don't print generated identifier numbers");
      (FStar_Getopt.noshort, "hide_uvar_nums",
        (FStar_Getopt.ZeroArgs ((fun uu____1430  -> Bool true))),
        "Don't print unification variable numbers");
      (FStar_Getopt.noshort, "hint_info",
        (FStar_Getopt.ZeroArgs ((fun uu____1438  -> Bool true))),
        "Print information regarding hints");
      (FStar_Getopt.noshort, "hint_file",
        (FStar_Getopt.OneArg (((fun _0_37  -> Path _0_37)), "[path]")),
        "Read/write hints to <path> (instead of module-specific hints files)");
      (FStar_Getopt.noshort, "in",
        (FStar_Getopt.ZeroArgs ((fun uu____1454  -> Bool true))),
        "Legacy interactive mode; reads input from stdin");
      (FStar_Getopt.noshort, "ide",
        (FStar_Getopt.ZeroArgs ((fun uu____1462  -> Bool true))),
        "JSON-based interactive mode for IDEs");
      (FStar_Getopt.noshort, "include",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1474 =
                  let uu____1476 =
                    let uu____1478 = get_include () in
                    FStar_List.map (fun _0_38  -> String _0_38) uu____1478 in
                  FStar_List.append uu____1476 [Path s] in
                List uu____1474)), "[path]")),
        "A directory in which to search for files included on the command line");
      (FStar_Getopt.noshort, "indent",
        (FStar_Getopt.ZeroArgs ((fun uu____1487  -> Bool true))),
        "Parses and outputs the files on the command line");
      (FStar_Getopt.noshort, "initial_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1499 = FStar_Util.int_of_string x in Int uu____1499)),
             "[non-negative integer]")),
        "Number of unrolling of recursive functions to try initially (default 2)");
      (FStar_Getopt.noshort, "initial_ifuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1511 = FStar_Util.int_of_string x in Int uu____1511)),
             "[non-negative integer]")),
        "Number of unrolling of inductive datatypes to try at first (default 1)");
      (FStar_Getopt.noshort, "inline_arith",
        (FStar_Getopt.ZeroArgs ((fun uu____1519  -> Bool true))),
        "Inline definitions of arithmetic functions in the SMT encoding");
      (FStar_Getopt.noshort, "lax",
        (FStar_Getopt.ZeroArgs ((fun uu____1527  -> Bool true))),
        "Run the lax-type checker only (admit all verification conditions)");
      (FStar_Getopt.noshort, "load",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1539 =
                  let uu____1541 =
                    let uu____1543 = get_load () in
                    FStar_List.map (fun _0_39  -> String _0_39) uu____1543 in
                  FStar_List.append uu____1541 [Path s] in
                List uu____1539)), "[module]")), "Load compiled module");
      (FStar_Getopt.noshort, "log_types",
        (FStar_Getopt.ZeroArgs ((fun uu____1552  -> Bool true))),
        "Print types computed for data/val/let-bindings");
      (FStar_Getopt.noshort, "log_queries",
        (FStar_Getopt.ZeroArgs ((fun uu____1560  -> Bool true))),
        "Log the Z3 queries in several queries-*.smt2 files, as we go");
      (FStar_Getopt.noshort, "max_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1572 = FStar_Util.int_of_string x in Int uu____1572)),
             "[non-negative integer]")),
        "Number of unrolling of recursive functions to try at most (default 8)");
      (FStar_Getopt.noshort, "max_ifuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1584 = FStar_Util.int_of_string x in Int uu____1584)),
             "[non-negative integer]")),
        "Number of unrolling of inductive datatypes to try at most (default 2)");
      (FStar_Getopt.noshort, "min_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1596 = FStar_Util.int_of_string x in Int uu____1596)),
             "[non-negative integer]")),
        "Minimum number of unrolling of recursive functions to try (default 1)");
      (FStar_Getopt.noshort, "MLish",
        (FStar_Getopt.ZeroArgs ((fun uu____1604  -> Bool true))),
        "Trigger various specializations for compiling the F* compiler itself (not meant for user code)");
      (FStar_Getopt.noshort, "n_cores",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1616 = FStar_Util.int_of_string x in Int uu____1616)),
             "[positive integer]")),
        "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)");
      (FStar_Getopt.noshort, "no_default_includes",
        (FStar_Getopt.ZeroArgs ((fun uu____1624  -> Bool true))),
        "Ignore the default module search paths");
      (FStar_Getopt.noshort, "no_extract",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1636 =
                  let uu____1638 =
                    let uu____1640 = get_no_extract () in x :: uu____1640 in
                  FStar_All.pipe_right uu____1638
                    (FStar_List.map (fun _0_40  -> String _0_40)) in
                List uu____1636)), "[module name]")),
        "Do not extract code from this module");
      (FStar_Getopt.noshort, "no_location_info",
        (FStar_Getopt.ZeroArgs ((fun uu____1651  -> Bool true))),
        "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)");
      (FStar_Getopt.noshort, "odir",
        (FStar_Getopt.OneArg
           (((fun p  -> let uu____1663 = validate_dir p in Path uu____1663)),
             "[dir]")), "Place output in directory [dir]");
      (FStar_Getopt.noshort, "prims",
        (FStar_Getopt.OneArg (((fun _0_41  -> String _0_41)), "file")), "");
      (FStar_Getopt.noshort, "print_bound_var_types",
        (FStar_Getopt.ZeroArgs ((fun uu____1679  -> Bool true))),
        "Print the types of bound variables");
      (FStar_Getopt.noshort, "print_effect_args",
        (FStar_Getopt.ZeroArgs ((fun uu____1687  -> Bool true))),
        "Print inferred predicate transformers for all computation types");
      (FStar_Getopt.noshort, "print_fuels",
        (FStar_Getopt.ZeroArgs ((fun uu____1695  -> Bool true))),
        "Print the fuel amounts used for each successful query");
      (FStar_Getopt.noshort, "print_full_names",
        (FStar_Getopt.ZeroArgs ((fun uu____1703  -> Bool true))),
        "Print full names of variables");
      (FStar_Getopt.noshort, "print_implicits",
        (FStar_Getopt.ZeroArgs ((fun uu____1711  -> Bool true))),
        "Print implicit arguments");
      (FStar_Getopt.noshort, "print_universes",
        (FStar_Getopt.ZeroArgs ((fun uu____1719  -> Bool true))),
        "Print universes");
      (FStar_Getopt.noshort, "print_z3_statistics",
        (FStar_Getopt.ZeroArgs ((fun uu____1727  -> Bool true))),
        "Print Z3 statistics for each SMT query");
      (FStar_Getopt.noshort, "prn",
        (FStar_Getopt.ZeroArgs ((fun uu____1735  -> Bool true))),
        "Print full names (deprecated; use --print_full_names instead)");
      (FStar_Getopt.noshort, "record_hints",
        (FStar_Getopt.ZeroArgs ((fun uu____1743  -> Bool true))),
        "Record a database of hints for efficient proof replay");
      (FStar_Getopt.noshort, "check_hints",
        (FStar_Getopt.ZeroArgs ((fun uu____1751  -> Bool true))),
        "Check new hints for replayability");
      (FStar_Getopt.noshort, "reuse_hint_for",
        (FStar_Getopt.OneArg
           (((fun _0_42  -> String _0_42)),
             "top-level name in the current module")),
        "Optimistically, attempt using the recorded hint for 'f' when trying to verify some other term 'g'");
      (FStar_Getopt.noshort, "show_signatures",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1771 =
                  let uu____1773 =
                    let uu____1775 = get_show_signatures () in x ::
                      uu____1775 in
                  FStar_All.pipe_right uu____1773
                    (FStar_List.map (fun _0_43  -> String _0_43)) in
                List uu____1771)), "[module name]")),
        "Show the checked signatures for all top-level symbols in the module");
      (FStar_Getopt.noshort, "silent",
        (FStar_Getopt.ZeroArgs ((fun uu____1786  -> Bool true))), " ");
      (FStar_Getopt.noshort, "smt",
        (FStar_Getopt.OneArg (((fun _0_44  -> Path _0_44)), "[path]")),
        "Path to the Z3 SMT solver (we could eventually support other solvers)");
      (FStar_Getopt.noshort, "smtencoding.elim_box",
        (FStar_Getopt.OneArg
           ((string_as_bool "smtencoding.elim_box"), "true|false")),
        "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')");
      (FStar_Getopt.noshort, "smtencoding.nl_arith_repr",
        (FStar_Getopt.OneArg
           (((fun _0_45  -> String _0_45)), "native|wrapped|boxwrap")),
        "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')");
      (FStar_Getopt.noshort, "smtencoding.l_arith_repr",
        (FStar_Getopt.OneArg
           (((fun _0_46  -> String _0_46)), "native|boxwrap")),
        "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')");
      (FStar_Getopt.noshort, "split_cases",
        (FStar_Getopt.OneArg
           (((fun n1  ->
                let uu____1830 = FStar_Util.int_of_string n1 in
                Int uu____1830)), "[positive integer]")),
        "Partition VC of a match into groups of [n] cases");
      (FStar_Getopt.noshort, "timing",
        (FStar_Getopt.ZeroArgs ((fun uu____1838  -> Bool true))),
        "Print the time it takes to verify each top-level definition");
      (FStar_Getopt.noshort, "trace_error",
        (FStar_Getopt.ZeroArgs ((fun uu____1846  -> Bool true))),
        "Don't print an error message; show an exception trace instead");
      (FStar_Getopt.noshort, "ugly",
        (FStar_Getopt.ZeroArgs ((fun uu____1854  -> Bool true))),
        "Emit output formatted for debugging");
      (FStar_Getopt.noshort, "unthrottle_inductives",
        (FStar_Getopt.ZeroArgs ((fun uu____1862  -> Bool true))),
        "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)");
      (FStar_Getopt.noshort, "use_eq_at_higher_order",
        (FStar_Getopt.ZeroArgs ((fun uu____1870  -> Bool true))),
        "Use equality constraints when comparing higher-order types (Temporary)");
      (FStar_Getopt.noshort, "use_hints",
        (FStar_Getopt.ZeroArgs ((fun uu____1878  -> Bool true))),
        "Use a previously recorded hints database for proof replay");
      (FStar_Getopt.noshort, "no_tactics",
        (FStar_Getopt.ZeroArgs ((fun uu____1886  -> Bool true))),
        "Do not run the tactic engine before discharging a VC");
      (FStar_Getopt.noshort, "using_facts_from",
        (FStar_Getopt.OneArg (cons_using_facts_from, "[namespace | fact id]")),
        "Implies --z3refresh; prunes the context to include facts from the given namespace of fact id (multiple uses of this option will prune the context to include those facts that match any of the provided namespaces / fact ids");
      (FStar_Getopt.noshort, "verify_all",
        (FStar_Getopt.ZeroArgs ((fun uu____1902  -> Bool true))),
        "With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.");
      (FStar_Getopt.noshort, "verify_module",
        (FStar_Getopt.OneArg (cons_verify_module, "[module name]")),
        "Name of the module to verify");
      (FStar_Getopt.noshort, "__temp_no_proj",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1922 =
                  let uu____1924 =
                    let uu____1926 = get___temp_no_proj () in x :: uu____1926 in
                  FStar_All.pipe_right uu____1924
                    (FStar_List.map (fun _0_47  -> String _0_47)) in
                List uu____1922)), "[module name]")),
        "Don't generate projectors for this module");
      ('v', "version",
        (FStar_Getopt.ZeroArgs
           ((fun uu____1938  ->
               display_version (); FStar_All.exit (Prims.parse_int "0")))),
        "Display version number");
      (FStar_Getopt.noshort, "warn_default_effects",
        (FStar_Getopt.ZeroArgs ((fun uu____1947  -> Bool true))),
        "Warn when (a -> b) is desugared to (a -> Tot b)");
      (FStar_Getopt.noshort, "z3cliopt",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1959 =
                  let uu____1961 =
                    let uu____1963 = get_z3cliopt () in
                    FStar_List.append uu____1963 [s] in
                  FStar_All.pipe_right uu____1961
                    (FStar_List.map (fun _0_48  -> String _0_48)) in
                List uu____1959)), "[option]")), "Z3 command line options");
      (FStar_Getopt.noshort, "z3refresh",
        (FStar_Getopt.ZeroArgs ((fun uu____1974  -> Bool true))),
        "Restart Z3 after each query; useful for ensuring proof robustness");
      (FStar_Getopt.noshort, "z3rlimit",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1986 = FStar_Util.int_of_string s in Int uu____1986)),
             "[positive integer]")),
        "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)");
      (FStar_Getopt.noshort, "z3rlimit_factor",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1998 = FStar_Util.int_of_string s in Int uu____1998)),
             "[positive integer]")),
        "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)");
      (FStar_Getopt.noshort, "z3seed",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____2010 = FStar_Util.int_of_string s in Int uu____2010)),
             "[positive integer]")), "Set the Z3 random seed (default 0)");
      (FStar_Getopt.noshort, "__no_positivity",
        (FStar_Getopt.ZeroArgs ((fun uu____2018  -> Bool true))),
        "Don't check positivity of inductive types")] in
    let uu____2024 = FStar_List.map mk_spec specs1 in
    ('h', "help",
      (FStar_Getopt.ZeroArgs
         (fun x  ->
            display_usage_aux specs1; FStar_All.exit (Prims.parse_int "0"))),
      "Display this information") :: uu____2024
and parse_codegen: Prims.string -> Prims.string =
  fun s  ->
    match s with
    | "Kremlin" -> s
    | "OCaml" -> s
    | "FSharp" -> s
    | uu____2047 ->
        (FStar_Util.print_string "Wrong argument to codegen flag\n";
         (let uu____2050 = specs () in display_usage_aux uu____2050);
         FStar_All.exit (Prims.parse_int "1"))
and string_as_bool: Prims.string -> Prims.string -> option_val =
  fun option_name  ->
    fun uu___55_2058  ->
      match uu___55_2058 with
      | "true" -> Bool true
      | "false" -> Bool false
      | uu____2059 ->
          (FStar_Util.print1 "Wrong argument to %s\n" option_name;
           (let uu____2062 = specs () in display_usage_aux uu____2062);
           FStar_All.exit (Prims.parse_int "1"))
and validate_dir: Prims.string -> Prims.string =
  fun p  -> FStar_Util.mkdir false p; p
let docs:
  Prims.unit ->
    (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2077  ->
    let uu____2078 = specs () in
    FStar_List.map
      (fun uu____2097  ->
         match uu____2097 with
         | (uu____2105,name,uu____2107,doc) -> (name, doc)) uu____2078
let settable: Prims.string -> Prims.bool =
  fun uu___56_2114  ->
    match uu___56_2114 with
    | "admit_smt_queries" -> true
    | "admit_except" -> true
    | "debug" -> true
    | "debug_level" -> true
    | "detail_errors" -> true
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
    | "print_fuels" -> true
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
    | uu____2115 -> false
let resettable: Prims.string -> Prims.bool =
  fun s  -> ((settable s) || (s = "z3seed")) || (s = "z3cliopt")
let all_specs: FStar_Getopt.opt Prims.list = specs ()
let settable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____2144  ->
          match uu____2144 with
          | (uu____2150,x,uu____2152,uu____2153) -> settable x))
let resettable_specs:
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____2179  ->
          match uu____2179 with
          | (uu____2185,x,uu____2187,uu____2188) -> resettable x))
let display_usage: Prims.unit -> Prims.unit =
  fun uu____2194  ->
    let uu____2195 = specs () in display_usage_aux uu____2195
let fstar_home: Prims.unit -> Prims.string =
  fun uu____2205  ->
    let uu____2206 = get_fstar_home () in
    match uu____2206 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        (set_option' ("fstar_home", (String x1)); x1)
    | FStar_Pervasives_Native.Some x -> x
exception File_argument of Prims.string
let uu___is_File_argument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____2219 -> true
    | uu____2220 -> false
let __proj__File_argument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____2228 -> uu____2228
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
            (fun s1  -> raise (File_argument s1)) s
      with
      | File_argument s1 ->
          let uu____2262 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____2262
let file_list_: Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let parse_cmd_line:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____2274  ->
    let res =
      let uu____2276 = specs () in
      FStar_Getopt.parse_cmdline uu____2276
        (fun i  ->
           let uu____2281 =
             let uu____2283 = FStar_ST.read file_list_ in
             FStar_List.append uu____2283 [i] in
           FStar_ST.write file_list_ uu____2281) in
    let uu____2291 =
      let uu____2293 = FStar_ST.read file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____2293 in
    (res, uu____2291)
let file_list: Prims.unit -> Prims.string Prims.list =
  fun uu____2303  -> FStar_ST.read file_list_
let restore_cmd_line_options: Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____2316 = specs () in
       FStar_Getopt.parse_cmdline uu____2316 (fun x  -> ()) in
     (let uu____2321 =
        let uu____2324 =
          let uu____2325 =
            FStar_List.map (fun _0_49  -> String _0_49) old_verify_module in
          List uu____2325 in
        ("verify_module", uu____2324) in
      set_option' uu____2321);
     r)
let should_verify: Prims.string -> Prims.bool =
  fun m  ->
    let uu____2331 = get_lax () in
    if uu____2331
    then false
    else
      (let uu____2333 = get_verify_all () in
       if uu____2333
       then true
       else
         (let uu____2335 = get_verify_module () in
          match uu____2335 with
          | [] ->
              let uu____2337 = file_list () in
              FStar_List.existsML
                (fun f  ->
                   let f1 = FStar_Util.basename f in
                   let f2 =
                     let uu____2345 =
                       let uu____2346 =
                         let uu____2347 =
                           let uu____2348 = FStar_Util.get_file_extension f1 in
                           FStar_String.length uu____2348 in
                         (FStar_String.length f1) - uu____2347 in
                       uu____2346 - (Prims.parse_int "1") in
                     FStar_String.substring f1 (Prims.parse_int "0")
                       uu____2345 in
                   (FStar_String.lowercase f2) = m) uu____2337
          | l -> FStar_List.contains (FStar_String.lowercase m) l))
let dont_gen_projectors: Prims.string -> Prims.bool =
  fun m  ->
    let uu____2363 = get___temp_no_proj () in
    FStar_List.contains m uu____2363
let should_print_message: Prims.string -> Prims.bool =
  fun m  ->
    let uu____2369 = should_verify m in
    if uu____2369 then m <> "Prims" else false
let include_path: Prims.unit -> Prims.string Prims.list =
  fun uu____2375  ->
    let uu____2376 = get_no_default_includes () in
    if uu____2376
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____2382 =
         let uu____2384 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____2384
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____2392 =
         let uu____2394 = get_include () in
         FStar_List.append uu____2394 ["."] in
       FStar_List.append uu____2382 uu____2392)
let find_file: Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun filename  ->
    let uu____2401 = FStar_Util.is_path_absolute filename in
    if uu____2401
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____2406 =
         let uu____2408 = include_path () in FStar_List.rev uu____2408 in
       FStar_Util.find_map uu____2406
         (fun p  ->
            let path = FStar_Util.join_paths p filename in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
let prims: Prims.unit -> Prims.string =
  fun uu____2419  ->
    let uu____2420 = get_prims () in
    match uu____2420 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst" in
        let uu____2423 = find_file filename in
        (match uu____2423 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____2426 =
               let uu____2427 =
                 FStar_Util.format1
                   "unable to find required file \"%s\" in the module search path.\n"
                   filename in
               FStar_Util.Failure uu____2427 in
             raise uu____2426)
    | FStar_Pervasives_Native.Some x -> x
let prims_basename: Prims.unit -> Prims.string =
  fun uu____2432  ->
    let uu____2433 = prims () in FStar_Util.basename uu____2433
let pervasives: Prims.unit -> Prims.string =
  fun uu____2437  ->
    let filename = "FStar.Pervasives.fst" in
    let uu____2439 = find_file filename in
    match uu____2439 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____2442 =
          let uu____2443 =
            FStar_Util.format1
              "unable to find required file \"%s\" in the module search path.\n"
              filename in
          FStar_Util.Failure uu____2443 in
        raise uu____2442
let pervasives_basename: Prims.unit -> Prims.string =
  fun uu____2447  ->
    let uu____2448 = pervasives () in FStar_Util.basename uu____2448
let pervasives_native_basename: Prims.unit -> Prims.string =
  fun uu____2452  ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____2454 = find_file filename in
    match uu____2454 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____2457 =
          let uu____2458 =
            FStar_Util.format1
              "unable to find required file \"%s\" in the module search path.\n"
              filename in
          FStar_Util.Failure uu____2458 in
        raise uu____2457
let prepend_output_dir: Prims.string -> Prims.string =
  fun fname  ->
    let uu____2463 = get_odir () in
    match uu____2463 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x ->
        Prims.strcat x (Prims.strcat "/" fname)
let __temp_no_proj: Prims.string -> Prims.bool =
  fun s  ->
    let uu____2470 = get___temp_no_proj () in
    FStar_All.pipe_right uu____2470 (FStar_List.contains s)
let admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____2476  -> get_admit_smt_queries ()
let admit_except: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____2481  -> get_admit_except ()
let check_hints: Prims.unit -> Prims.bool =
  fun uu____2485  -> get_check_hints ()
let codegen: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____2490  -> get_codegen ()
let codegen_libs: Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____2496  ->
    let uu____2497 = get_codegen_lib () in
    FStar_All.pipe_right uu____2497
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
let debug_any: Prims.unit -> Prims.bool =
  fun uu____2508  -> let uu____2509 = get_debug () in uu____2509 <> []
let debug_at_level: Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      ((modul = "") ||
         (let uu____2521 = get_debug () in
          FStar_All.pipe_right uu____2521 (FStar_List.contains modul)))
        && (debug_level_geq level)
let dep: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____2528  -> get_dep ()
let detail_errors: Prims.unit -> Prims.bool =
  fun uu____2532  -> get_detail_errors ()
let doc: Prims.unit -> Prims.bool = fun uu____2536  -> get_doc ()
let dump_module: Prims.string -> Prims.bool =
  fun s  ->
    let uu____2541 = get_dump_module () in
    FStar_All.pipe_right uu____2541 (FStar_List.contains s)
let eager_inference: Prims.unit -> Prims.bool =
  fun uu____2547  -> get_eager_inference ()
let explicit_deps: Prims.unit -> Prims.bool =
  fun uu____2551  -> get_explicit_deps ()
let extract_all: Prims.unit -> Prims.bool =
  fun uu____2555  -> get_extract_all ()
let fs_typ_app: Prims.string -> Prims.bool =
  fun filename  ->
    let uu____2560 = FStar_ST.read light_off_files in
    FStar_List.contains filename uu____2560
let full_context_dependency: Prims.unit -> Prims.bool =
  fun uu____2568  -> true
let hide_genident_nums: Prims.unit -> Prims.bool =
  fun uu____2572  -> get_hide_genident_nums ()
let hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____2576  -> get_hide_uvar_nums ()
let hint_info: Prims.unit -> Prims.bool = fun uu____2580  -> get_hint_info ()
let hint_file: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____2585  -> get_hint_file ()
let ide: Prims.unit -> Prims.bool = fun uu____2589  -> get_ide ()
let indent: Prims.unit -> Prims.bool = fun uu____2593  -> get_indent ()
let initial_fuel: Prims.unit -> Prims.int =
  fun uu____2597  ->
    let uu____2598 = get_initial_fuel () in
    let uu____2599 = get_max_fuel () in Prims.min uu____2598 uu____2599
let initial_ifuel: Prims.unit -> Prims.int =
  fun uu____2603  ->
    let uu____2604 = get_initial_ifuel () in
    let uu____2605 = get_max_ifuel () in Prims.min uu____2604 uu____2605
let interactive: Prims.unit -> Prims.bool =
  fun uu____2609  -> (get_in ()) || (get_ide ())
let lax: Prims.unit -> Prims.bool = fun uu____2613  -> get_lax ()
let load: Prims.unit -> Prims.string Prims.list =
  fun uu____2618  -> get_load ()
let legacy_interactive: Prims.unit -> Prims.bool =
  fun uu____2622  -> get_in ()
let log_queries: Prims.unit -> Prims.bool =
  fun uu____2626  -> get_log_queries ()
let log_types: Prims.unit -> Prims.bool = fun uu____2630  -> get_log_types ()
let max_fuel: Prims.unit -> Prims.int = fun uu____2634  -> get_max_fuel ()
let max_ifuel: Prims.unit -> Prims.int = fun uu____2638  -> get_max_ifuel ()
let min_fuel: Prims.unit -> Prims.int = fun uu____2642  -> get_min_fuel ()
let ml_ish: Prims.unit -> Prims.bool = fun uu____2646  -> get_MLish ()
let set_ml_ish: Prims.unit -> Prims.unit =
  fun uu____2650  -> set_option "MLish" (Bool true)
let n_cores: Prims.unit -> Prims.int = fun uu____2654  -> get_n_cores ()
let no_default_includes: Prims.unit -> Prims.bool =
  fun uu____2658  -> get_no_default_includes ()
let no_extract: Prims.string -> Prims.bool =
  fun s  ->
    let uu____2663 = get_no_extract () in
    FStar_All.pipe_right uu____2663 (FStar_List.contains s)
let no_location_info: Prims.unit -> Prims.bool =
  fun uu____2669  -> get_no_location_info ()
let output_dir: Prims.unit -> Prims.string FStar_Pervasives_Native.option =
  fun uu____2674  -> get_odir ()
let ugly: Prims.unit -> Prims.bool = fun uu____2678  -> get_ugly ()
let print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____2682  -> get_print_bound_var_types ()
let print_effect_args: Prims.unit -> Prims.bool =
  fun uu____2686  -> get_print_effect_args ()
let print_fuels: Prims.unit -> Prims.bool =
  fun uu____2690  -> get_print_fuels ()
let print_implicits: Prims.unit -> Prims.bool =
  fun uu____2694  -> get_print_implicits ()
let print_real_names: Prims.unit -> Prims.bool =
  fun uu____2698  -> (get_prn ()) || (get_print_full_names ())
let print_universes: Prims.unit -> Prims.bool =
  fun uu____2702  -> get_print_universes ()
let print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____2706  -> get_print_z3_statistics ()
let record_hints: Prims.unit -> Prims.bool =
  fun uu____2710  -> get_record_hints ()
let reuse_hint_for: Prims.unit -> Prims.string FStar_Pervasives_Native.option
  = fun uu____2715  -> get_reuse_hint_for ()
let silent: Prims.unit -> Prims.bool = fun uu____2719  -> get_silent ()
let smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____2723  -> get_smtencoding_elim_box ()
let smtencoding_nl_arith_native: Prims.unit -> Prims.bool =
  fun uu____2727  ->
    let uu____2728 = get_smtencoding_nl_arith_repr () in
    uu____2728 = "native"
let smtencoding_nl_arith_wrapped: Prims.unit -> Prims.bool =
  fun uu____2732  ->
    let uu____2733 = get_smtencoding_nl_arith_repr () in
    uu____2733 = "wrapped"
let smtencoding_nl_arith_default: Prims.unit -> Prims.bool =
  fun uu____2737  ->
    let uu____2738 = get_smtencoding_nl_arith_repr () in
    uu____2738 = "boxwrap"
let smtencoding_l_arith_native: Prims.unit -> Prims.bool =
  fun uu____2742  ->
    let uu____2743 = get_smtencoding_l_arith_repr () in uu____2743 = "native"
let smtencoding_l_arith_default: Prims.unit -> Prims.bool =
  fun uu____2747  ->
    let uu____2748 = get_smtencoding_l_arith_repr () in
    uu____2748 = "boxwrap"
let split_cases: Prims.unit -> Prims.int =
  fun uu____2752  -> get_split_cases ()
let timing: Prims.unit -> Prims.bool = fun uu____2756  -> get_timing ()
let trace_error: Prims.unit -> Prims.bool =
  fun uu____2760  -> get_trace_error ()
let unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____2764  -> get_unthrottle_inductives ()
let use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____2768  -> get_use_eq_at_higher_order ()
let use_hints: Prims.unit -> Prims.bool = fun uu____2772  -> get_use_hints ()
let use_tactics: Prims.unit -> Prims.bool =
  fun uu____2776  -> get_use_tactics ()
let using_facts_from:
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun uu____2782  -> get_using_facts_from ()
let verify_all: Prims.unit -> Prims.bool =
  fun uu____2786  -> get_verify_all ()
let verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____2791  -> get_verify_module ()
let warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____2795  -> get_warn_default_effects ()
let z3_exe: Prims.unit -> Prims.string =
  fun uu____2799  ->
    let uu____2800 = get_smt () in
    match uu____2800 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let z3_cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____2807  -> get_z3cliopt ()
let z3_refresh: Prims.unit -> Prims.bool =
  fun uu____2811  -> get_z3refresh ()
let z3_rlimit: Prims.unit -> Prims.int = fun uu____2815  -> get_z3rlimit ()
let z3_rlimit_factor: Prims.unit -> Prims.int =
  fun uu____2819  -> get_z3rlimit_factor ()
let z3_seed: Prims.unit -> Prims.int = fun uu____2823  -> get_z3seed ()
let no_positivity: Prims.unit -> Prims.bool =
  fun uu____2827  -> get_no_positivity ()
let should_extract: Prims.string -> Prims.bool =
  fun m  ->
    (let uu____2834 = no_extract m in Prims.op_Negation uu____2834) &&
      ((extract_all ()) ||
         (let uu____2837 = get_extract_module () in
          match uu____2837 with
          | [] ->
              let uu____2839 = get_extract_namespace () in
              (match uu____2839 with
               | [] -> true
               | ns ->
                   FStar_Util.for_some
                     (FStar_Util.starts_with (FStar_String.lowercase m)) ns)
          | l -> FStar_List.contains (FStar_String.lowercase m) l))