open Prims
type debug_level_t =
  | Low
  | Medium
  | High
  | Extreme
  | Other of Prims.string
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
  | Unset
let uu___is_Bool: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____58 -> false
let __proj__Bool__item___0: option_val -> Prims.bool =
  fun projectee  -> match projectee with | Bool _0 -> _0
let uu___is_String: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____70 -> false
let __proj__String__item___0: option_val -> Prims.string =
  fun projectee  -> match projectee with | String _0 -> _0
let uu___is_Path: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____82 -> false
let __proj__Path__item___0: option_val -> Prims.string =
  fun projectee  -> match projectee with | Path _0 -> _0
let uu___is_Int: option_val -> Prims.bool =
  fun projectee  -> match projectee with | Int _0 -> true | uu____94 -> false
let __proj__Int__item___0: option_val -> Prims.int =
  fun projectee  -> match projectee with | Int _0 -> _0
let uu___is_List: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____107 -> false
let __proj__List__item___0: option_val -> option_val Prims.list =
  fun projectee  -> match projectee with | List _0 -> _0
let uu___is_Unset: option_val -> Prims.bool =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____121 -> false
type options =
  | Set
  | Reset
  | Restore
let uu___is_Set: options -> Prims.bool =
  fun projectee  -> match projectee with | Set  -> true | uu____125 -> false
let uu___is_Reset: options -> Prims.bool =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____129 -> false
let uu___is_Restore: options -> Prims.bool =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____133 -> false
let __unit_tests__: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let __unit_tests: Prims.unit -> Prims.bool =
  fun uu____139  -> FStar_ST.read __unit_tests__
let __set_unit_tests: Prims.unit -> Prims.unit =
  fun uu____144  -> FStar_ST.write __unit_tests__ true
let __clear_unit_tests: Prims.unit -> Prims.unit =
  fun uu____149  -> FStar_ST.write __unit_tests__ false
let as_bool: option_val -> Prims.bool =
  fun uu___49_154  ->
    match uu___49_154 with
    | Bool b -> b
    | uu____156 -> failwith "Impos: expected Bool"
let as_int: option_val -> Prims.int =
  fun uu___50_159  ->
    match uu___50_159 with
    | Int b -> b
    | uu____161 -> failwith "Impos: expected Int"
let as_string: option_val -> Prims.string =
  fun uu___51_164  ->
    match uu___51_164 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____167 -> failwith "Impos: expected String"
let as_list as_t uu___52_183 =
  match uu___52_183 with
  | List ts -> FStar_All.pipe_right ts (FStar_List.map as_t)
  | uu____190 -> failwith "Impos: expected List"
let as_option as_t uu___53_207 =
  match uu___53_207 with
  | Unset  -> None
  | v1 -> let uu____211 = as_t v1 in Some uu____211
let fstar_options: option_val FStar_Util.smap Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let peek: Prims.unit -> option_val FStar_Util.smap =
  fun uu____223  ->
    let uu____224 = FStar_ST.read fstar_options in FStar_List.hd uu____224
let pop: Prims.unit -> Prims.unit =
  fun uu____234  ->
    let uu____235 = FStar_ST.read fstar_options in
    match uu____235 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____243::[] -> failwith "TOO MANY POPS!"
    | uu____247::tl1 -> FStar_ST.write fstar_options tl1
let push: Prims.unit -> Prims.unit =
  fun uu____259  ->
    let uu____260 =
      let uu____263 =
        let uu____265 = peek () in FStar_Util.smap_copy uu____265 in
      let uu____267 = FStar_ST.read fstar_options in uu____263 :: uu____267 in
    FStar_ST.write fstar_options uu____260
let set_option: Prims.string -> option_val -> Prims.unit =
  fun k  ->
    fun v1  -> let uu____285 = peek () in FStar_Util.smap_add uu____285 k v1
let set_option': (Prims.string* option_val) -> Prims.unit =
  fun uu____291  -> match uu____291 with | (k,v1) -> set_option k v1
let with_saved_options f = push (); (let retv = f () in pop (); retv)
let light_off_files: Prims.string Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let add_light_off_file: Prims.string -> Prims.unit =
  fun filename  ->
    let uu____319 =
      let uu____321 = FStar_ST.read light_off_files in filename :: uu____321 in
    FStar_ST.write light_off_files uu____319
let defaults: (Prims.string* option_val) Prims.list =
  [("__temp_no_proj", (List []));
  ("_fstar_home", (String ""));
  ("_include_path", (List []));
  ("admit_smt_queries", (Bool false));
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
  ("in", (Bool false));
  ("ide", (Bool false));
  ("include", (List []));
  ("indent", (Bool false));
  ("initial_fuel", (Int (Prims.parse_int "2")));
  ("initial_ifuel", (Int (Prims.parse_int "1")));
  ("lax", (Bool false));
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
  ("z3timeout", (Int (Prims.parse_int "5")));
  ("z3cliopt", (List []));
  ("__no_positivity", (Bool false))]
let init: Prims.unit -> Prims.unit =
  fun uu____498  ->
    let o = peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let clear: Prims.unit -> Prims.unit =
  fun uu____509  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50") in
    FStar_ST.write fstar_options [o];
    FStar_ST.write light_off_files [];
    init ()
let _run: Prims.unit = clear ()
let get_option: Prims.string -> option_val =
  fun s  ->
    let uu____526 =
      let uu____528 = peek () in FStar_Util.smap_try_find uu____528 s in
    match uu____526 with
    | None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | Some s1 -> s1
let lookup_opt s c = c (get_option s)
let get_admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____550  -> lookup_opt "admit_smt_queries" as_bool
let get_check_hints: Prims.unit -> Prims.bool =
  fun uu____553  -> lookup_opt "check_hints" as_bool
let get_codegen: Prims.unit -> Prims.string option =
  fun uu____557  -> lookup_opt "codegen" (as_option as_string)
let get_codegen_lib: Prims.unit -> Prims.string Prims.list =
  fun uu____562  -> lookup_opt "codegen-lib" (as_list as_string)
let get_debug: Prims.unit -> Prims.string Prims.list =
  fun uu____567  -> lookup_opt "debug" (as_list as_string)
let get_debug_level: Prims.unit -> Prims.string Prims.list =
  fun uu____572  -> lookup_opt "debug_level" (as_list as_string)
let get_dep: Prims.unit -> Prims.string option =
  fun uu____577  -> lookup_opt "dep" (as_option as_string)
let get_detail_errors: Prims.unit -> Prims.bool =
  fun uu____581  -> lookup_opt "detail_errors" as_bool
let get_doc: Prims.unit -> Prims.bool =
  fun uu____584  -> lookup_opt "doc" as_bool
let get_dump_module: Prims.unit -> Prims.string Prims.list =
  fun uu____588  -> lookup_opt "dump_module" (as_list as_string)
let get_eager_inference: Prims.unit -> Prims.bool =
  fun uu____592  -> lookup_opt "eager_inference" as_bool
let get_explicit_deps: Prims.unit -> Prims.bool =
  fun uu____595  -> lookup_opt "explicit_deps" as_bool
let get_extract_all: Prims.unit -> Prims.bool =
  fun uu____598  -> lookup_opt "extract_all" as_bool
let get_extract_module: Prims.unit -> Prims.string Prims.list =
  fun uu____602  -> lookup_opt "extract_module" (as_list as_string)
let get_extract_namespace: Prims.unit -> Prims.string Prims.list =
  fun uu____607  -> lookup_opt "extract_namespace" (as_list as_string)
let get_fs_typ_app: Prims.unit -> Prims.bool =
  fun uu____611  -> lookup_opt "fs_typ_app" as_bool
let get_fstar_home: Prims.unit -> Prims.string option =
  fun uu____615  -> lookup_opt "fstar_home" (as_option as_string)
let get_hide_genident_nums: Prims.unit -> Prims.bool =
  fun uu____619  -> lookup_opt "hide_genident_nums" as_bool
let get_hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____622  -> lookup_opt "hide_uvar_nums" as_bool
let get_hint_info: Prims.unit -> Prims.bool =
  fun uu____625  -> lookup_opt "hint_info" as_bool
let get_in: Prims.unit -> Prims.bool =
  fun uu____628  -> lookup_opt "in" as_bool
let get_ide: Prims.unit -> Prims.bool =
  fun uu____631  -> lookup_opt "ide" as_bool
let get_include: Prims.unit -> Prims.string Prims.list =
  fun uu____635  -> lookup_opt "include" (as_list as_string)
let get_indent: Prims.unit -> Prims.bool =
  fun uu____639  -> lookup_opt "indent" as_bool
let get_initial_fuel: Prims.unit -> Prims.int =
  fun uu____642  -> lookup_opt "initial_fuel" as_int
let get_initial_ifuel: Prims.unit -> Prims.int =
  fun uu____645  -> lookup_opt "initial_ifuel" as_int
let get_lax: Prims.unit -> Prims.bool =
  fun uu____648  -> lookup_opt "lax" as_bool
let get_log_queries: Prims.unit -> Prims.bool =
  fun uu____651  -> lookup_opt "log_queries" as_bool
let get_log_types: Prims.unit -> Prims.bool =
  fun uu____654  -> lookup_opt "log_types" as_bool
let get_max_fuel: Prims.unit -> Prims.int =
  fun uu____657  -> lookup_opt "max_fuel" as_int
let get_max_ifuel: Prims.unit -> Prims.int =
  fun uu____660  -> lookup_opt "max_ifuel" as_int
let get_min_fuel: Prims.unit -> Prims.int =
  fun uu____663  -> lookup_opt "min_fuel" as_int
let get_MLish: Prims.unit -> Prims.bool =
  fun uu____666  -> lookup_opt "MLish" as_bool
let get_n_cores: Prims.unit -> Prims.int =
  fun uu____669  -> lookup_opt "n_cores" as_int
let get_no_default_includes: Prims.unit -> Prims.bool =
  fun uu____672  -> lookup_opt "no_default_includes" as_bool
let get_no_extract: Prims.unit -> Prims.string Prims.list =
  fun uu____676  -> lookup_opt "no_extract" (as_list as_string)
let get_no_location_info: Prims.unit -> Prims.bool =
  fun uu____680  -> lookup_opt "no_location_info" as_bool
let get_odir: Prims.unit -> Prims.string option =
  fun uu____684  -> lookup_opt "odir" (as_option as_string)
let get_ugly: Prims.unit -> Prims.bool =
  fun uu____688  -> lookup_opt "ugly" as_bool
let get_prims: Prims.unit -> Prims.string option =
  fun uu____692  -> lookup_opt "prims" (as_option as_string)
let get_print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____696  -> lookup_opt "print_bound_var_types" as_bool
let get_print_effect_args: Prims.unit -> Prims.bool =
  fun uu____699  -> lookup_opt "print_effect_args" as_bool
let get_print_fuels: Prims.unit -> Prims.bool =
  fun uu____702  -> lookup_opt "print_fuels" as_bool
let get_print_full_names: Prims.unit -> Prims.bool =
  fun uu____705  -> lookup_opt "print_full_names" as_bool
let get_print_implicits: Prims.unit -> Prims.bool =
  fun uu____708  -> lookup_opt "print_implicits" as_bool
let get_print_universes: Prims.unit -> Prims.bool =
  fun uu____711  -> lookup_opt "print_universes" as_bool
let get_print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____714  -> lookup_opt "print_z3_statistics" as_bool
let get_prn: Prims.unit -> Prims.bool =
  fun uu____717  -> lookup_opt "prn" as_bool
let get_record_hints: Prims.unit -> Prims.bool =
  fun uu____720  -> lookup_opt "record_hints" as_bool
let get_reuse_hint_for: Prims.unit -> Prims.string option =
  fun uu____724  -> lookup_opt "reuse_hint_for" (as_option as_string)
let get_show_signatures: Prims.unit -> Prims.string Prims.list =
  fun uu____729  -> lookup_opt "show_signatures" (as_list as_string)
let get_silent: Prims.unit -> Prims.bool =
  fun uu____733  -> lookup_opt "silent" as_bool
let get_smt: Prims.unit -> Prims.string option =
  fun uu____737  -> lookup_opt "smt" (as_option as_string)
let get_smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____741  -> lookup_opt "smtencoding.elim_box" as_bool
let get_smtencoding_nl_arith_repr: Prims.unit -> Prims.string =
  fun uu____744  -> lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr: Prims.unit -> Prims.string =
  fun uu____747  -> lookup_opt "smtencoding.l_arith_repr" as_string
let get_split_cases: Prims.unit -> Prims.int =
  fun uu____750  -> lookup_opt "split_cases" as_int
let get_timing: Prims.unit -> Prims.bool =
  fun uu____753  -> lookup_opt "timing" as_bool
let get_trace_error: Prims.unit -> Prims.bool =
  fun uu____756  -> lookup_opt "trace_error" as_bool
let get_unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____759  -> lookup_opt "unthrottle_inductives" as_bool
let get_use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____762  -> lookup_opt "use_eq_at_higher_order" as_bool
let get_use_hints: Prims.unit -> Prims.bool =
  fun uu____765  -> lookup_opt "use_hints" as_bool
let get_use_tactics: Prims.unit -> Prims.bool =
  fun uu____768  ->
    let uu____769 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____769
let get_using_facts_from: Prims.unit -> Prims.string Prims.list option =
  fun uu____774  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let get_verify_all: Prims.unit -> Prims.bool =
  fun uu____780  -> lookup_opt "verify_all" as_bool
let get_verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____784  -> lookup_opt "verify_module" (as_list as_string)
let get___temp_no_proj: Prims.unit -> Prims.string Prims.list =
  fun uu____789  -> lookup_opt "__temp_no_proj" (as_list as_string)
let get_version: Prims.unit -> Prims.bool =
  fun uu____793  -> lookup_opt "version" as_bool
let get_warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____796  -> lookup_opt "warn_default_effects" as_bool
let get_z3cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____800  -> lookup_opt "z3cliopt" (as_list as_string)
let get_z3refresh: Prims.unit -> Prims.bool =
  fun uu____804  -> lookup_opt "z3refresh" as_bool
let get_z3rlimit: Prims.unit -> Prims.int =
  fun uu____807  -> lookup_opt "z3rlimit" as_int
let get_z3rlimit_factor: Prims.unit -> Prims.int =
  fun uu____810  -> lookup_opt "z3rlimit_factor" as_int
let get_z3seed: Prims.unit -> Prims.int =
  fun uu____813  -> lookup_opt "z3seed" as_int
let get_z3timeout: Prims.unit -> Prims.int =
  fun uu____816  -> lookup_opt "z3timeout" as_int
let get_no_positivity: Prims.unit -> Prims.bool =
  fun uu____819  -> lookup_opt "__no_positivity" as_bool
let dlevel: Prims.string -> debug_level_t =
  fun uu___54_822  ->
    match uu___54_822 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let one_debug_level_geq: debug_level_t -> debug_level_t -> Prims.bool =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____830 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let debug_level_geq: debug_level_t -> Prims.bool =
  fun l2  ->
    let uu____834 = get_debug_level () in
    FStar_All.pipe_right uu____834
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
let universe_include_path_base_dirs: Prims.string Prims.list =
  ["/ulib"; "/lib/fstar"]
let _version: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _platform: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _compiler: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _date: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let _commit: Prims.string FStar_ST.ref = FStar_Util.mk_ref ""
let display_version: Prims.unit -> Prims.unit =
  fun uu____861  ->
    let uu____862 =
      let uu____863 = FStar_ST.read _version in
      let uu____866 = FStar_ST.read _platform in
      let uu____869 = FStar_ST.read _compiler in
      let uu____872 = FStar_ST.read _date in
      let uu____875 = FStar_ST.read _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____863
        uu____866 uu____869 uu____872 uu____875 in
    FStar_Util.print_string uu____862
let display_usage_aux specs =
  FStar_Util.print_string "fstar.exe [options] file[s]\n";
  FStar_List.iter
    (fun uu____905  ->
       match uu____905 with
       | (uu____911,flag,p,doc) ->
           (match p with
            | FStar_Getopt.ZeroArgs ig ->
                if doc = ""
                then
                  let uu____920 =
                    let uu____921 = FStar_Util.colorize_bold flag in
                    FStar_Util.format1 "  --%s\n" uu____921 in
                  FStar_Util.print_string uu____920
                else
                  (let uu____923 =
                     let uu____924 = FStar_Util.colorize_bold flag in
                     FStar_Util.format2 "  --%s  %s\n" uu____924 doc in
                   FStar_Util.print_string uu____923)
            | FStar_Getopt.OneArg (uu____925,argname) ->
                if doc = ""
                then
                  let uu____931 =
                    let uu____932 = FStar_Util.colorize_bold flag in
                    let uu____933 = FStar_Util.colorize_bold argname in
                    FStar_Util.format2 "  --%s %s\n" uu____932 uu____933 in
                  FStar_Util.print_string uu____931
                else
                  (let uu____935 =
                     let uu____936 = FStar_Util.colorize_bold flag in
                     let uu____937 = FStar_Util.colorize_bold argname in
                     FStar_Util.format3 "  --%s %s  %s\n" uu____936 uu____937
                       doc in
                   FStar_Util.print_string uu____935))) specs
let mk_spec:
  (FStar_BaseTypes.char* Prims.string* option_val FStar_Getopt.opt_variant*
    Prims.string) -> FStar_Getopt.opt
  =
  fun o  ->
    let uu____951 = o in
    match uu____951 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____972 =
                let uu____973 = let uu____976 = f () in (name, uu____976) in
                set_option' uu____973 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x =
                let uu____987 = let uu____990 = f x in (name, uu____990) in
                set_option' uu____987 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let cons_extract_module: Prims.string -> option_val =
  fun s  ->
    let uu____997 =
      let uu____999 =
        let uu____1001 = get_extract_module () in (FStar_String.lowercase s)
          :: uu____1001 in
      FStar_All.pipe_right uu____999
        (FStar_List.map (fun _0_25  -> String _0_25)) in
    List uu____997
let cons_extract_namespace: Prims.string -> option_val =
  fun s  ->
    let uu____1008 =
      let uu____1010 =
        let uu____1012 = get_extract_namespace () in
        (FStar_String.lowercase s) :: uu____1012 in
      FStar_All.pipe_right uu____1010
        (FStar_List.map (fun _0_26  -> String _0_26)) in
    List uu____1008
let add_extract_module: Prims.string -> Prims.unit =
  fun s  ->
    let uu____1019 = cons_extract_module s in
    set_option "extract_module" uu____1019
let add_extract_namespace: Prims.string -> Prims.unit =
  fun s  ->
    let uu____1023 = cons_extract_namespace s in
    set_option "extract_namespace" uu____1023
let cons_verify_module: Prims.string -> option_val =
  fun s  ->
    let uu____1027 =
      let uu____1029 =
        let uu____1031 = get_verify_module () in (FStar_String.lowercase s)
          :: uu____1031 in
      FStar_All.pipe_right uu____1029
        (FStar_List.map (fun _0_27  -> String _0_27)) in
    List uu____1027
let cons_using_facts_from: Prims.string -> option_val =
  fun s  ->
    set_option "z3refresh" (Bool true);
    (let uu____1039 = get_using_facts_from () in
     match uu____1039 with
     | None  -> List [String s]
     | Some l ->
         let uu____1046 =
           FStar_List.map (fun _0_28  -> String _0_28) (s :: l) in
         List uu____1046)
let add_verify_module: Prims.string -> Prims.unit =
  fun s  ->
    let uu____1051 = cons_verify_module s in
    set_option "verify_module" uu____1051
let rec specs:
  Prims.unit ->
    (FStar_Char.char* Prims.string* Prims.unit FStar_Getopt.opt_variant*
      Prims.string) Prims.list
  =
  fun uu____1063  ->
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
      (FStar_Getopt.noshort, "codegen",
        (FStar_Getopt.OneArg
           (((fun s  -> let uu____1092 = parse_codegen s in String uu____1092)),
             "[OCaml|FSharp|Kremlin]")), "Generate code for execution");
      (FStar_Getopt.noshort, "codegen-lib",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1102 =
                  let uu____1104 =
                    let uu____1106 = get_codegen_lib () in s :: uu____1106 in
                  FStar_All.pipe_right uu____1104
                    (FStar_List.map (fun _0_29  -> String _0_29)) in
                List uu____1102)), "[namespace]")),
        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)");
      (FStar_Getopt.noshort, "debug",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1119 =
                  let uu____1121 =
                    let uu____1123 = get_debug () in x :: uu____1123 in
                  FStar_All.pipe_right uu____1121
                    (FStar_List.map (fun _0_30  -> String _0_30)) in
                List uu____1119)), "[module name]")),
        "Print lots of debugging information while checking module");
      (FStar_Getopt.noshort, "debug_level",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1136 =
                  let uu____1138 =
                    let uu____1140 = get_debug_level () in x :: uu____1140 in
                  FStar_All.pipe_right uu____1138
                    (FStar_List.map (fun _0_31  -> String _0_31)) in
                List uu____1136)), "[Low|Medium|High|Extreme|...]")),
        "Control the verbosity of debugging info");
      (FStar_Getopt.noshort, "dep",
        (FStar_Getopt.OneArg
           (((fun x  ->
                if (x = "make") || (x = "graph")
                then String x
                else failwith "invalid argument to 'dep'")), "[make|graph]")),
        "Output the transitive closure of the dependency graph in a format suitable for the given tool");
      (FStar_Getopt.noshort, "detail_errors",
        (FStar_Getopt.ZeroArgs ((fun uu____1160  -> Bool true))),
        "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1");
      (FStar_Getopt.noshort, "doc",
        (FStar_Getopt.ZeroArgs ((fun uu____1167  -> Bool true))),
        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.");
      (FStar_Getopt.noshort, "dump_module",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1177 =
                  let uu____1179 =
                    let uu____1181 = get_dump_module () in x :: uu____1181 in
                  FStar_All.pipe_right uu____1179
                    (FStar_List.map (fun _0_32  -> String _0_32)) in
                FStar_All.pipe_right uu____1177 (fun _0_33  -> List _0_33))),
             "[module name]")), "");
      (FStar_Getopt.noshort, "eager_inference",
        (FStar_Getopt.ZeroArgs ((fun uu____1192  -> Bool true))),
        "Solve all type-inference constraints eagerly; more efficient but at the cost of generality");
      (FStar_Getopt.noshort, "explicit_deps",
        (FStar_Getopt.ZeroArgs ((fun uu____1199  -> Bool true))),
        "Do not find dependencies automatically, the user provides them on the command-line");
      (FStar_Getopt.noshort, "extract_all",
        (FStar_Getopt.ZeroArgs ((fun uu____1206  -> Bool true))),
        "Discover the complete dependency graph and do not stop at interface boundaries");
      (FStar_Getopt.noshort, "extract_module",
        (FStar_Getopt.OneArg (cons_extract_module, "[module name]")),
        "Only extract the specified modules (instead of the possibly-partial dependency graph)");
      (FStar_Getopt.noshort, "extract_namespace",
        (FStar_Getopt.OneArg (cons_extract_namespace, "[namespace name]")),
        "Only extract modules in the specified namespace");
      (FStar_Getopt.noshort, "fstar_home",
        (FStar_Getopt.OneArg (((fun _0_34  -> Path _0_34)), "[dir]")),
        "Set the FSTAR_HOME variable to [dir]");
      (FStar_Getopt.noshort, "hide_genident_nums",
        (FStar_Getopt.ZeroArgs ((fun uu____1237  -> Bool true))),
        "Don't print generated identifier numbers");
      (FStar_Getopt.noshort, "hide_uvar_nums",
        (FStar_Getopt.ZeroArgs ((fun uu____1244  -> Bool true))),
        "Don't print unification variable numbers");
      (FStar_Getopt.noshort, "hint_info",
        (FStar_Getopt.ZeroArgs ((fun uu____1251  -> Bool true))),
        "Print information regarding hints");
      (FStar_Getopt.noshort, "in",
        (FStar_Getopt.ZeroArgs ((fun uu____1258  -> Bool true))),
        "Legacy interactive mode; reads input from stdin");
      (FStar_Getopt.noshort, "ide",
        (FStar_Getopt.ZeroArgs ((fun uu____1265  -> Bool true))),
        "JSON-based interactive mode for IDEs");
      (FStar_Getopt.noshort, "include",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1275 =
                  let uu____1277 =
                    let uu____1279 = get_include () in
                    FStar_List.map (fun _0_35  -> String _0_35) uu____1279 in
                  FStar_List.append uu____1277 [Path s] in
                List uu____1275)), "[path]")),
        "A directory in which to search for files included on the command line");
      (FStar_Getopt.noshort, "indent",
        (FStar_Getopt.ZeroArgs ((fun uu____1287  -> Bool true))),
        "Parses and outputs the files on the command line");
      (FStar_Getopt.noshort, "initial_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1297 = FStar_Util.int_of_string x in Int uu____1297)),
             "[non-negative integer]")),
        "Number of unrolling of recursive functions to try initially (default 2)");
      (FStar_Getopt.noshort, "initial_ifuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1307 = FStar_Util.int_of_string x in Int uu____1307)),
             "[non-negative integer]")),
        "Number of unrolling of inductive datatypes to try at first (default 1)");
      (FStar_Getopt.noshort, "inline_arith",
        (FStar_Getopt.ZeroArgs ((fun uu____1314  -> Bool true))),
        "Inline definitions of arithmetic functions in the SMT encoding");
      (FStar_Getopt.noshort, "lax",
        (FStar_Getopt.ZeroArgs ((fun uu____1321  -> Bool true))),
        "Run the lax-type checker only (admit all verification conditions)");
      (FStar_Getopt.noshort, "log_types",
        (FStar_Getopt.ZeroArgs ((fun uu____1328  -> Bool true))),
        "Print types computed for data/val/let-bindings");
      (FStar_Getopt.noshort, "log_queries",
        (FStar_Getopt.ZeroArgs ((fun uu____1335  -> Bool true))),
        "Log the Z3 queries in several queries-*.smt2 files, as we go");
      (FStar_Getopt.noshort, "max_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1345 = FStar_Util.int_of_string x in Int uu____1345)),
             "[non-negative integer]")),
        "Number of unrolling of recursive functions to try at most (default 8)");
      (FStar_Getopt.noshort, "max_ifuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1355 = FStar_Util.int_of_string x in Int uu____1355)),
             "[non-negative integer]")),
        "Number of unrolling of inductive datatypes to try at most (default 2)");
      (FStar_Getopt.noshort, "min_fuel",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1365 = FStar_Util.int_of_string x in Int uu____1365)),
             "[non-negative integer]")),
        "Minimum number of unrolling of recursive functions to try (default 1)");
      (FStar_Getopt.noshort, "MLish",
        (FStar_Getopt.ZeroArgs ((fun uu____1372  -> Bool true))),
        "Trigger various specializations for compiling the F* compiler itself (not meant for user code)");
      (FStar_Getopt.noshort, "n_cores",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1382 = FStar_Util.int_of_string x in Int uu____1382)),
             "[positive integer]")),
        "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)");
      (FStar_Getopt.noshort, "no_default_includes",
        (FStar_Getopt.ZeroArgs ((fun uu____1389  -> Bool true))),
        "Ignore the default module search paths");
      (FStar_Getopt.noshort, "no_extract",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1399 =
                  let uu____1401 =
                    let uu____1403 = get_no_extract () in x :: uu____1403 in
                  FStar_All.pipe_right uu____1401
                    (FStar_List.map (fun _0_36  -> String _0_36)) in
                List uu____1399)), "[module name]")),
        "Do not extract code from this module");
      (FStar_Getopt.noshort, "no_location_info",
        (FStar_Getopt.ZeroArgs ((fun uu____1413  -> Bool true))),
        "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)");
      (FStar_Getopt.noshort, "odir",
        (FStar_Getopt.OneArg
           (((fun p  -> let uu____1423 = validate_dir p in Path uu____1423)),
             "[dir]")), "Place output in directory [dir]");
      (FStar_Getopt.noshort, "prims",
        (FStar_Getopt.OneArg (((fun _0_37  -> String _0_37)), "file")), "");
      (FStar_Getopt.noshort, "print_bound_var_types",
        (FStar_Getopt.ZeroArgs ((fun uu____1438  -> Bool true))),
        "Print the types of bound variables");
      (FStar_Getopt.noshort, "print_effect_args",
        (FStar_Getopt.ZeroArgs ((fun uu____1445  -> Bool true))),
        "Print inferred predicate transformers for all computation types");
      (FStar_Getopt.noshort, "print_fuels",
        (FStar_Getopt.ZeroArgs ((fun uu____1452  -> Bool true))),
        "Print the fuel amounts used for each successful query");
      (FStar_Getopt.noshort, "print_full_names",
        (FStar_Getopt.ZeroArgs ((fun uu____1459  -> Bool true))),
        "Print full names of variables");
      (FStar_Getopt.noshort, "print_implicits",
        (FStar_Getopt.ZeroArgs ((fun uu____1466  -> Bool true))),
        "Print implicit arguments");
      (FStar_Getopt.noshort, "print_universes",
        (FStar_Getopt.ZeroArgs ((fun uu____1473  -> Bool true))),
        "Print universes");
      (FStar_Getopt.noshort, "print_z3_statistics",
        (FStar_Getopt.ZeroArgs ((fun uu____1480  -> Bool true))),
        "Print Z3 statistics for each SMT query");
      (FStar_Getopt.noshort, "prn",
        (FStar_Getopt.ZeroArgs ((fun uu____1487  -> Bool true))),
        "Print full names (deprecated; use --print_full_names instead)");
      (FStar_Getopt.noshort, "record_hints",
        (FStar_Getopt.ZeroArgs ((fun uu____1494  -> Bool true))),
        "Record a database of hints for efficient proof replay");
      (FStar_Getopt.noshort, "check_hints",
        (FStar_Getopt.ZeroArgs ((fun uu____1501  -> Bool true))),
        "Check new hints for replayability");
      (FStar_Getopt.noshort, "reuse_hint_for",
        (FStar_Getopt.OneArg
           (((fun _0_38  -> String _0_38)),
             "top-level name in the current module")),
        "Optimistically, attempt using the recorded hint for 'f' when trying to verify some other term 'g'");
      (FStar_Getopt.noshort, "show_signatures",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1519 =
                  let uu____1521 =
                    let uu____1523 = get_show_signatures () in x ::
                      uu____1523 in
                  FStar_All.pipe_right uu____1521
                    (FStar_List.map (fun _0_39  -> String _0_39)) in
                List uu____1519)), "[module name]")),
        "Show the checked signatures for all top-level symbols in the module");
      (FStar_Getopt.noshort, "silent",
        (FStar_Getopt.ZeroArgs ((fun uu____1533  -> Bool true))), " ");
      (FStar_Getopt.noshort, "smt",
        (FStar_Getopt.OneArg (((fun _0_40  -> Path _0_40)), "[path]")),
        "Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)");
      (FStar_Getopt.noshort, "smtencoding.elim_box",
        (FStar_Getopt.OneArg
           ((string_as_bool "smtencoding.elim_box"), "true|false")),
        "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')");
      (FStar_Getopt.noshort, "smtencoding.nl_arith_repr",
        (FStar_Getopt.OneArg
           (((fun _0_41  -> String _0_41)), "native|wrapped|boxwrap")),
        "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')");
      (FStar_Getopt.noshort, "smtencoding.l_arith_repr",
        (FStar_Getopt.OneArg
           (((fun _0_42  -> String _0_42)), "native|boxwrap")),
        "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')");
      (FStar_Getopt.noshort, "split_cases",
        (FStar_Getopt.OneArg
           (((fun n1  ->
                let uu____1575 = FStar_Util.int_of_string n1 in
                Int uu____1575)), "[positive integer]")),
        "Partition VC of a match into groups of [n] cases");
      (FStar_Getopt.noshort, "timing",
        (FStar_Getopt.ZeroArgs ((fun uu____1582  -> Bool true))),
        "Print the time it takes to verify each top-level definition");
      (FStar_Getopt.noshort, "trace_error",
        (FStar_Getopt.ZeroArgs ((fun uu____1589  -> Bool true))),
        "Don't print an error message; show an exception trace instead");
      (FStar_Getopt.noshort, "ugly",
        (FStar_Getopt.ZeroArgs ((fun uu____1596  -> Bool true))),
        "Emit output formatted for debugging");
      (FStar_Getopt.noshort, "unthrottle_inductives",
        (FStar_Getopt.ZeroArgs ((fun uu____1603  -> Bool true))),
        "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)");
      (FStar_Getopt.noshort, "use_eq_at_higher_order",
        (FStar_Getopt.ZeroArgs ((fun uu____1610  -> Bool true))),
        "Use equality constraints when comparing higher-order types (Temporary)");
      (FStar_Getopt.noshort, "use_hints",
        (FStar_Getopt.ZeroArgs ((fun uu____1617  -> Bool true))),
        "Use a previously recorded hints database for proof replay");
      (FStar_Getopt.noshort, "no_tactics",
        (FStar_Getopt.ZeroArgs ((fun uu____1624  -> Bool true))),
        "Do not run the tactic engine before discharging a VC");
      (FStar_Getopt.noshort, "using_facts_from",
        (FStar_Getopt.OneArg (cons_using_facts_from, "[namespace | fact id]")),
        "Implies --z3refresh; prunes the context to include facts from the given namespace of fact id (multiple uses of this option will prune the context to include those facts that match any of the provided namespaces / fact ids");
      (FStar_Getopt.noshort, "verify_all",
        (FStar_Getopt.ZeroArgs ((fun uu____1639  -> Bool true))),
        "With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.");
      (FStar_Getopt.noshort, "verify_module",
        (FStar_Getopt.OneArg (cons_verify_module, "[module name]")),
        "Name of the module to verify");
      (FStar_Getopt.noshort, "__temp_no_proj",
        (FStar_Getopt.OneArg
           (((fun x  ->
                let uu____1657 =
                  let uu____1659 =
                    let uu____1661 = get___temp_no_proj () in x :: uu____1661 in
                  FStar_All.pipe_right uu____1659
                    (FStar_List.map (fun _0_43  -> String _0_43)) in
                List uu____1657)), "[module name]")),
        "Don't generate projectors for this module");
      ('v', "version",
        (FStar_Getopt.ZeroArgs
           ((fun uu____1671  ->
               display_version (); FStar_All.exit (Prims.parse_int "0")))),
        "Display version number");
      (FStar_Getopt.noshort, "warn_default_effects",
        (FStar_Getopt.ZeroArgs ((fun uu____1679  -> Bool true))),
        "Warn when (a -> b) is desugared to (a -> Tot b)");
      (FStar_Getopt.noshort, "z3cliopt",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1689 =
                  let uu____1691 =
                    let uu____1693 = get_z3cliopt () in
                    FStar_List.append uu____1693 [s] in
                  FStar_All.pipe_right uu____1691
                    (FStar_List.map (fun _0_44  -> String _0_44)) in
                List uu____1689)), "[option]")), "Z3 command line options");
      (FStar_Getopt.noshort, "z3refresh",
        (FStar_Getopt.ZeroArgs ((fun uu____1703  -> Bool true))),
        "Restart Z3 after each query; useful for ensuring proof robustness");
      (FStar_Getopt.noshort, "z3rlimit",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1713 = FStar_Util.int_of_string s in Int uu____1713)),
             "[positive integer]")),
        "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)");
      (FStar_Getopt.noshort, "z3rlimit_factor",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1723 = FStar_Util.int_of_string s in Int uu____1723)),
             "[positive integer]")),
        "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)");
      (FStar_Getopt.noshort, "z3seed",
        (FStar_Getopt.OneArg
           (((fun s  ->
                let uu____1733 = FStar_Util.int_of_string s in Int uu____1733)),
             "[positive integer]")), "Set the Z3 random seed (default 0)");
      (FStar_Getopt.noshort, "z3timeout",
        (FStar_Getopt.OneArg
           (((fun s  ->
                FStar_Util.print_string
                  "Warning: z3timeout ignored; use z3rlimit instead\n";
                (let uu____1744 = FStar_Util.int_of_string s in
                 Int uu____1744))), "[positive integer]")),
        "Set the Z3 per-query (soft) timeout to [t] seconds (default 5)");
      (FStar_Getopt.noshort, "__no_positivity",
        (FStar_Getopt.ZeroArgs ((fun uu____1751  -> Bool true))),
        "Don't check positivity of inductive types")] in
    let uu____1757 = FStar_List.map mk_spec specs1 in
    ('h', "help",
      (FStar_Getopt.ZeroArgs
         (fun x  ->
            display_usage_aux specs1; FStar_All.exit (Prims.parse_int "0"))),
      "Display this information") :: uu____1757
and parse_codegen: Prims.string -> Prims.string =
  fun s  ->
    match s with
    | "Kremlin" -> s
    | "OCaml" -> s
    | "FSharp" -> s
    | uu____1778 ->
        (FStar_Util.print_string "Wrong argument to codegen flag\n";
         (let uu____1781 = specs () in display_usage_aux uu____1781);
         FStar_All.exit (Prims.parse_int "1"))
and string_as_bool: Prims.string -> Prims.string -> option_val =
  fun option_name  ->
    fun uu___55_1789  ->
      match uu___55_1789 with
      | "true" -> Bool true
      | "false" -> Bool false
      | uu____1790 ->
          (FStar_Util.print1 "Wrong argument to %s\n" option_name;
           (let uu____1793 = specs () in display_usage_aux uu____1793);
           FStar_All.exit (Prims.parse_int "1"))
and validate_dir: Prims.string -> Prims.string =
  fun p  -> FStar_Util.mkdir false p; p
let docs: Prims.unit -> (Prims.string* Prims.string) Prims.list =
  fun uu____1807  ->
    let uu____1808 = specs () in
    FStar_List.map
      (fun uu____1822  ->
         match uu____1822 with
         | (uu____1830,name,uu____1832,doc) -> (name, doc)) uu____1808
let settable: Prims.string -> Prims.bool =
  fun uu___56_1838  ->
    match uu___56_1838 with
    | "admit_smt_queries" -> true
    | "debug" -> true
    | "debug_level" -> true
    | "detail_errors" -> true
    | "eager_inference" -> true
    | "hide_genident_nums" -> true
    | "hide_uvar_nums" -> true
    | "hint_info" -> true
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
    | uu____1839 -> false
let resettable: Prims.string -> Prims.bool =
  fun s  ->
    (((settable s) || (s = "z3timeout")) || (s = "z3seed")) ||
      (s = "z3cliopt")
let all_specs: FStar_Getopt.opt Prims.list = specs ()
let settable_specs:
  (FStar_BaseTypes.char* Prims.string* Prims.unit FStar_Getopt.opt_variant*
    Prims.string) Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____1862  ->
          match uu____1862 with
          | (uu____1868,x,uu____1870,uu____1871) -> settable x))
let resettable_specs:
  (FStar_BaseTypes.char* Prims.string* Prims.unit FStar_Getopt.opt_variant*
    Prims.string) Prims.list
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____1892  ->
          match uu____1892 with
          | (uu____1898,x,uu____1900,uu____1901) -> resettable x))
let display_usage: Prims.unit -> Prims.unit =
  fun uu____1906  ->
    let uu____1907 = specs () in display_usage_aux uu____1907
let fstar_home: Prims.unit -> Prims.string =
  fun uu____1916  ->
    let uu____1917 = get_fstar_home () in
    match uu____1917 with
    | None  ->
        let x = FStar_Util.get_exec_dir () in
        let x1 = Prims.strcat x "/.." in
        (set_option' ("fstar_home", (String x1)); x1)
    | Some x -> x
exception File_argument of Prims.string
let uu___is_File_argument: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | File_argument uu____1929 -> true
    | uu____1930 -> false
let __proj__File_argument__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | File_argument uu____1937 -> uu____1937
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
          let uu____1963 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____1963
let file_list_: Prims.string Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let parse_cmd_line:
  Prims.unit -> (FStar_Getopt.parse_cmdline_res* Prims.string Prims.list) =
  fun uu____1974  ->
    let res =
      let uu____1976 = specs () in
      FStar_Getopt.parse_cmdline uu____1976
        (fun i  ->
           let uu____1979 =
             let uu____1981 = FStar_ST.read file_list_ in
             FStar_List.append uu____1981 [i] in
           FStar_ST.write file_list_ uu____1979) in
    let uu____1989 =
      let uu____1991 = FStar_ST.read file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____1991 in
    (res, uu____1989)
let file_list: Prims.unit -> Prims.string Prims.list =
  fun uu____2000  -> FStar_ST.read file_list_
let restore_cmd_line_options: Prims.bool -> FStar_Getopt.parse_cmdline_res =
  fun should_clear  ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____2012 = specs () in
       FStar_Getopt.parse_cmdline uu____2012 (fun x  -> ()) in
     (let uu____2016 =
        let uu____2019 =
          let uu____2020 =
            FStar_List.map (fun _0_45  -> String _0_45) old_verify_module in
          List uu____2020 in
        ("verify_module", uu____2019) in
      set_option' uu____2016);
     r)
let should_verify: Prims.string -> Prims.bool =
  fun m  ->
    let uu____2025 = get_lax () in
    if uu____2025
    then false
    else
      (let uu____2027 = get_verify_all () in
       if uu____2027
       then true
       else
         (let uu____2029 = get_verify_module () in
          match uu____2029 with
          | [] ->
              let uu____2031 = file_list () in
              FStar_List.existsML
                (fun f  ->
                   let f1 = FStar_Util.basename f in
                   let f2 =
                     let uu____2036 =
                       let uu____2037 =
                         let uu____2038 =
                           let uu____2039 = FStar_Util.get_file_extension f1 in
                           FStar_String.length uu____2039 in
                         (FStar_String.length f1) - uu____2038 in
                       uu____2037 - (Prims.parse_int "1") in
                     FStar_String.substring f1 (Prims.parse_int "0")
                       uu____2036 in
                   (FStar_String.lowercase f2) = m) uu____2031
          | l -> FStar_List.contains (FStar_String.lowercase m) l))
let dont_gen_projectors: Prims.string -> Prims.bool =
  fun m  ->
    let uu____2049 = get___temp_no_proj () in
    FStar_List.contains m uu____2049
let should_print_message: Prims.string -> Prims.bool =
  fun m  ->
    let uu____2054 = should_verify m in
    if uu____2054 then m <> "Prims" else false
let include_path: Prims.unit -> Prims.string Prims.list =
  fun uu____2059  ->
    let uu____2060 = get_no_default_includes () in
    if uu____2060
    then get_include ()
    else
      (let h = fstar_home () in
       let defs = universe_include_path_base_dirs in
       let uu____2066 =
         let uu____2068 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x)) in
         FStar_All.pipe_right uu____2068
           (FStar_List.filter FStar_Util.file_exists) in
       let uu____2075 =
         let uu____2077 = get_include () in
         FStar_List.append uu____2077 ["."] in
       FStar_List.append uu____2066 uu____2075)
let find_file: Prims.string -> Prims.string option =
  fun filename  ->
    let uu____2083 = FStar_Util.is_path_absolute filename in
    if uu____2083
    then (if FStar_Util.file_exists filename then Some filename else None)
    else
      (let uu____2088 =
         let uu____2090 = include_path () in FStar_List.rev uu____2090 in
       FStar_Util.find_map uu____2088
         (fun p  ->
            let path = FStar_Util.join_paths p filename in
            if FStar_Util.file_exists path then Some path else None))
let prims: Prims.unit -> Prims.string =
  fun uu____2098  ->
    let uu____2099 = get_prims () in
    match uu____2099 with
    | None  ->
        let filename = "prims.fst" in
        let uu____2102 = find_file filename in
        (match uu____2102 with
         | Some result -> result
         | None  ->
             let uu____2105 =
               let uu____2106 =
                 FStar_Util.format1
                   "unable to find required file \"%s\" in the module search path.\n"
                   filename in
               FStar_Util.Failure uu____2106 in
             raise uu____2105)
    | Some x -> x
let prims_basename: Prims.unit -> Prims.string =
  fun uu____2110  ->
    let uu____2111 = prims () in FStar_Util.basename uu____2111
let pervasives: Prims.unit -> Prims.string =
  fun uu____2114  ->
    let filename = "FStar.Pervasives.fst" in
    let uu____2116 = find_file filename in
    match uu____2116 with
    | Some result -> result
    | None  ->
        let uu____2119 =
          let uu____2120 =
            FStar_Util.format1
              "unable to find required file \"%s\" in the module search path.\n"
              filename in
          FStar_Util.Failure uu____2120 in
        raise uu____2119
let pervasives_basename: Prims.unit -> Prims.string =
  fun uu____2123  ->
    let uu____2124 = pervasives () in FStar_Util.basename uu____2124
let prepend_output_dir: Prims.string -> Prims.string =
  fun fname  ->
    let uu____2128 = get_odir () in
    match uu____2128 with
    | None  -> fname
    | Some x -> Prims.strcat x (Prims.strcat "/" fname)
let __temp_no_proj: Prims.string -> Prims.bool =
  fun s  ->
    let uu____2134 = get___temp_no_proj () in
    FStar_All.pipe_right uu____2134 (FStar_List.contains s)
let admit_smt_queries: Prims.unit -> Prims.bool =
  fun uu____2139  -> get_admit_smt_queries ()
let check_hints: Prims.unit -> Prims.bool =
  fun uu____2142  -> get_check_hints ()
let codegen: Prims.unit -> Prims.string option =
  fun uu____2146  -> get_codegen ()
let codegen_libs: Prims.unit -> Prims.string Prims.list Prims.list =
  fun uu____2151  ->
    let uu____2152 = get_codegen_lib () in
    FStar_All.pipe_right uu____2152
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
let debug_any: Prims.unit -> Prims.bool =
  fun uu____2161  -> let uu____2162 = get_debug () in uu____2162 <> []
let debug_at_level: Prims.string -> debug_level_t -> Prims.bool =
  fun modul  ->
    fun level  ->
      ((modul = "") ||
         (let uu____2171 = get_debug () in
          FStar_All.pipe_right uu____2171 (FStar_List.contains modul)))
        && (debug_level_geq level)
let dep: Prims.unit -> Prims.string option = fun uu____2177  -> get_dep ()
let detail_errors: Prims.unit -> Prims.bool =
  fun uu____2180  -> get_detail_errors ()
let doc: Prims.unit -> Prims.bool = fun uu____2183  -> get_doc ()
let dump_module: Prims.string -> Prims.bool =
  fun s  ->
    let uu____2187 = get_dump_module () in
    FStar_All.pipe_right uu____2187 (FStar_List.contains s)
let eager_inference: Prims.unit -> Prims.bool =
  fun uu____2192  -> get_eager_inference ()
let explicit_deps: Prims.unit -> Prims.bool =
  fun uu____2195  -> get_explicit_deps ()
let extract_all: Prims.unit -> Prims.bool =
  fun uu____2198  -> get_extract_all ()
let fs_typ_app: Prims.string -> Prims.bool =
  fun filename  ->
    let uu____2202 = FStar_ST.read light_off_files in
    FStar_List.contains filename uu____2202
let full_context_dependency: Prims.unit -> Prims.bool =
  fun uu____2209  -> true
let hide_genident_nums: Prims.unit -> Prims.bool =
  fun uu____2212  -> get_hide_genident_nums ()
let hide_uvar_nums: Prims.unit -> Prims.bool =
  fun uu____2215  -> get_hide_uvar_nums ()
let hint_info: Prims.unit -> Prims.bool = fun uu____2218  -> get_hint_info ()
let ide: Prims.unit -> Prims.bool = fun uu____2221  -> get_ide ()
let indent: Prims.unit -> Prims.bool = fun uu____2224  -> get_indent ()
let initial_fuel: Prims.unit -> Prims.int =
  fun uu____2227  ->
    let uu____2228 = get_initial_fuel () in
    let uu____2229 = get_max_fuel () in Prims.min uu____2228 uu____2229
let initial_ifuel: Prims.unit -> Prims.int =
  fun uu____2232  ->
    let uu____2233 = get_initial_ifuel () in
    let uu____2234 = get_max_ifuel () in Prims.min uu____2233 uu____2234
let interactive: Prims.unit -> Prims.bool =
  fun uu____2237  -> (get_in ()) || (get_ide ())
let lax: Prims.unit -> Prims.bool = fun uu____2240  -> get_lax ()
let legacy_interactive: Prims.unit -> Prims.bool =
  fun uu____2243  -> get_in ()
let log_queries: Prims.unit -> Prims.bool =
  fun uu____2246  -> get_log_queries ()
let log_types: Prims.unit -> Prims.bool = fun uu____2249  -> get_log_types ()
let max_fuel: Prims.unit -> Prims.int = fun uu____2252  -> get_max_fuel ()
let max_ifuel: Prims.unit -> Prims.int = fun uu____2255  -> get_max_ifuel ()
let min_fuel: Prims.unit -> Prims.int = fun uu____2258  -> get_min_fuel ()
let ml_ish: Prims.unit -> Prims.bool = fun uu____2261  -> get_MLish ()
let set_ml_ish: Prims.unit -> Prims.unit =
  fun uu____2264  -> set_option "MLish" (Bool true)
let n_cores: Prims.unit -> Prims.int = fun uu____2267  -> get_n_cores ()
let no_default_includes: Prims.unit -> Prims.bool =
  fun uu____2270  -> get_no_default_includes ()
let no_extract: Prims.string -> Prims.bool =
  fun s  ->
    let uu____2274 = get_no_extract () in
    FStar_All.pipe_right uu____2274 (FStar_List.contains s)
let no_location_info: Prims.unit -> Prims.bool =
  fun uu____2279  -> get_no_location_info ()
let output_dir: Prims.unit -> Prims.string option =
  fun uu____2283  -> get_odir ()
let ugly: Prims.unit -> Prims.bool = fun uu____2286  -> get_ugly ()
let print_bound_var_types: Prims.unit -> Prims.bool =
  fun uu____2289  -> get_print_bound_var_types ()
let print_effect_args: Prims.unit -> Prims.bool =
  fun uu____2292  -> get_print_effect_args ()
let print_fuels: Prims.unit -> Prims.bool =
  fun uu____2295  -> get_print_fuels ()
let print_implicits: Prims.unit -> Prims.bool =
  fun uu____2298  -> get_print_implicits ()
let print_real_names: Prims.unit -> Prims.bool =
  fun uu____2301  -> (get_prn ()) || (get_print_full_names ())
let print_universes: Prims.unit -> Prims.bool =
  fun uu____2304  -> get_print_universes ()
let print_z3_statistics: Prims.unit -> Prims.bool =
  fun uu____2307  -> get_print_z3_statistics ()
let record_hints: Prims.unit -> Prims.bool =
  fun uu____2310  -> get_record_hints ()
let reuse_hint_for: Prims.unit -> Prims.string option =
  fun uu____2314  -> get_reuse_hint_for ()
let silent: Prims.unit -> Prims.bool = fun uu____2317  -> get_silent ()
let smtencoding_elim_box: Prims.unit -> Prims.bool =
  fun uu____2320  -> get_smtencoding_elim_box ()
let smtencoding_nl_arith_native: Prims.unit -> Prims.bool =
  fun uu____2323  ->
    let uu____2324 = get_smtencoding_nl_arith_repr () in
    uu____2324 = "native"
let smtencoding_nl_arith_wrapped: Prims.unit -> Prims.bool =
  fun uu____2327  ->
    let uu____2328 = get_smtencoding_nl_arith_repr () in
    uu____2328 = "wrapped"
let smtencoding_nl_arith_default: Prims.unit -> Prims.bool =
  fun uu____2331  ->
    let uu____2332 = get_smtencoding_nl_arith_repr () in
    uu____2332 = "boxwrap"
let smtencoding_l_arith_native: Prims.unit -> Prims.bool =
  fun uu____2335  ->
    let uu____2336 = get_smtencoding_l_arith_repr () in uu____2336 = "native"
let smtencoding_l_arith_default: Prims.unit -> Prims.bool =
  fun uu____2339  ->
    let uu____2340 = get_smtencoding_l_arith_repr () in
    uu____2340 = "boxwrap"
let split_cases: Prims.unit -> Prims.int =
  fun uu____2343  -> get_split_cases ()
let timing: Prims.unit -> Prims.bool = fun uu____2346  -> get_timing ()
let trace_error: Prims.unit -> Prims.bool =
  fun uu____2349  -> get_trace_error ()
let unthrottle_inductives: Prims.unit -> Prims.bool =
  fun uu____2352  -> get_unthrottle_inductives ()
let use_eq_at_higher_order: Prims.unit -> Prims.bool =
  fun uu____2355  -> get_use_eq_at_higher_order ()
let use_hints: Prims.unit -> Prims.bool = fun uu____2358  -> get_use_hints ()
let use_tactics: Prims.unit -> Prims.bool =
  fun uu____2361  -> get_use_tactics ()
let using_facts_from: Prims.unit -> Prims.string Prims.list option =
  fun uu____2366  -> get_using_facts_from ()
let verify_all: Prims.unit -> Prims.bool =
  fun uu____2369  -> get_verify_all ()
let verify_module: Prims.unit -> Prims.string Prims.list =
  fun uu____2373  -> get_verify_module ()
let warn_default_effects: Prims.unit -> Prims.bool =
  fun uu____2376  -> get_warn_default_effects ()
let z3_exe: Prims.unit -> Prims.string =
  fun uu____2379  ->
    let uu____2380 = get_smt () in
    match uu____2380 with | None  -> FStar_Platform.exe "z3" | Some s -> s
let z3_cliopt: Prims.unit -> Prims.string Prims.list =
  fun uu____2386  -> get_z3cliopt ()
let z3_refresh: Prims.unit -> Prims.bool =
  fun uu____2389  -> get_z3refresh ()
let z3_rlimit: Prims.unit -> Prims.int = fun uu____2392  -> get_z3rlimit ()
let z3_rlimit_factor: Prims.unit -> Prims.int =
  fun uu____2395  -> get_z3rlimit_factor ()
let z3_seed: Prims.unit -> Prims.int = fun uu____2398  -> get_z3seed ()
let z3_timeout: Prims.unit -> Prims.int = fun uu____2401  -> get_z3timeout ()
let no_positivity: Prims.unit -> Prims.bool =
  fun uu____2404  -> get_no_positivity ()
let should_extract: Prims.string -> Prims.bool =
  fun m  ->
    (let uu____2408 = no_extract m in Prims.op_Negation uu____2408) &&
      ((extract_all ()) ||
         (let uu____2409 = get_extract_module () in
          match uu____2409 with
          | [] ->
              let uu____2411 = get_extract_namespace () in
              (match uu____2411 with
               | [] -> true
               | ns ->
                   FStar_Util.for_some
                     (FStar_Util.starts_with (FStar_String.lowercase m)) ns)
          | l -> FStar_List.contains (FStar_String.lowercase m) l))