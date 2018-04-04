open Prims
type debug_level_t =
  | Low 
  | Medium 
  | High 
  | Extreme 
  | Other of Prims.string [@@deriving show]
let (uu___is_Low : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | Low  -> true | uu____8 -> false 
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____12 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | High  -> true | uu____16 -> false 
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____20 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____25 -> false
  
let (__proj__Other__item___0 : debug_level_t -> Prims.string) =
  fun projectee  -> match projectee with | Other _0 -> _0 
type option_val =
  | Bool of Prims.bool 
  | String of Prims.string 
  | Path of Prims.string 
  | Int of Prims.int 
  | List of option_val Prims.list 
  | Unset [@@deriving show]
let (uu___is_Bool : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____59 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____71 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____83 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Int _0 -> true | uu____95 -> false 
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____109 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____126 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _0_27  -> Bool _0_27 
let (mk_string : Prims.string -> option_val) = fun _0_28  -> String _0_28 
let (mk_path : Prims.string -> option_val) = fun _0_29  -> Path _0_29 
let (mk_int : Prims.int -> option_val) = fun _0_30  -> Int _0_30 
let (mk_list : option_val Prims.list -> option_val) =
  fun _0_31  -> List _0_31 
type options =
  | Set 
  | Reset 
  | Restore [@@deriving show]
let (uu___is_Set : options -> Prims.bool) =
  fun projectee  -> match projectee with | Set  -> true | uu____142 -> false 
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____146 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____150 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : Prims.unit -> Prims.bool) =
  fun uu____166  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : Prims.unit -> Prims.unit) =
  fun uu____188  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : Prims.unit -> Prims.unit) =
  fun uu____210  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___38_232  ->
    match uu___38_232 with
    | Bool b -> b
    | uu____234 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___39_237  ->
    match uu___39_237 with
    | Int b -> b
    | uu____239 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___40_242  ->
    match uu___40_242 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____245 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___41_250  ->
    match uu___41_250 with
    | List ts -> ts
    | uu____256 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____262 .
    (option_val -> 'Auu____262) -> option_val -> 'Auu____262 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____278 = as_list' x  in
      FStar_All.pipe_right uu____278 (FStar_List.map as_t)
  
let as_option :
  'Auu____288 .
    (option_val -> 'Auu____288) ->
      option_val -> 'Auu____288 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___42_301  ->
      match uu___42_301 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____305 = as_t v1  in FStar_Pervasives_Native.Some uu____305
  
type optionstate = option_val FStar_Util.smap[@@deriving show]
let (fstar_options : optionstate Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : Prims.unit -> optionstate) =
  fun uu____327  ->
    let uu____328 = FStar_ST.op_Bang fstar_options  in
    FStar_List.hd uu____328
  
let (pop : Prims.unit -> Prims.unit) =
  fun uu____356  ->
    let uu____357 = FStar_ST.op_Bang fstar_options  in
    match uu____357 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____383::[] -> failwith "TOO MANY POPS!"
    | uu____384::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : Prims.unit -> Prims.unit) =
  fun uu____413  ->
    let uu____414 =
      let uu____417 =
        let uu____420 = peek ()  in FStar_Util.smap_copy uu____420  in
      let uu____423 = FStar_ST.op_Bang fstar_options  in uu____417 ::
        uu____423
       in
    FStar_ST.op_Colon_Equals fstar_options uu____414
  
let (set : optionstate -> Prims.unit) =
  fun o  ->
    let uu____479 = FStar_ST.op_Bang fstar_options  in
    match uu____479 with
    | [] -> failwith "set on empty option stack"
    | uu____505::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
  
let (set_option : Prims.string -> option_val -> Prims.unit) =
  fun k  ->
    fun v1  -> let uu____538 = peek ()  in FStar_Util.smap_add uu____538 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> Prims.unit) =
  fun uu____547  -> match uu____547 with | (k,v1) -> set_option k v1 
let with_saved_options : 'a . (Prims.unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f ()  in pop (); retv) 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> Prims.unit) =
  fun filename  ->
    let uu____589 =
      let uu____592 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____592
       in
    FStar_ST.op_Colon_Equals light_off_files uu____589
  
let (defaults :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 Prims.list) =
  [("__temp_no_proj", (List []));
  ("__temp_fast_implicits", (Bool false));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
  ("cache_checked_modules", (Bool false));
  ("cache_dir", Unset);
  ("codegen", Unset);
  ("codegen-lib", (List []));
  ("debug", (List []));
  ("debug_level", (List []));
  ("defensive", (String "no"));
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
  ("no_smt", (Bool false));
  ("no_tactics", (Bool false));
  ("normalize_pure_terms_for_extraction", (Bool false));
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
  ("warn_error", (String ""));
  ("use_extracted_interfaces", (Bool false))] 
let (init : Prims.unit -> Prims.unit) =
  fun uu____1029  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : Prims.unit -> Prims.unit) =
  fun uu____1044  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : Prims.unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1103 =
      let uu____1106 = peek ()  in FStar_Util.smap_try_find uu____1106 s  in
    match uu____1103 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1113 . Prims.string -> (option_val -> 'Auu____1113) -> 'Auu____1113
  = fun s  -> fun c  -> c (get_option s) 
let (get_admit_smt_queries : Prims.unit -> Prims.bool) =
  fun uu____1129  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1134  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : Prims.unit -> Prims.bool) =
  fun uu____1139  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1144  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_codegen : Prims.unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1151  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : Prims.unit -> Prims.string Prims.list) =
  fun uu____1158  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : Prims.unit -> Prims.string Prims.list) =
  fun uu____1165  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : Prims.unit -> Prims.string Prims.list) =
  fun uu____1172  -> lookup_opt "debug_level" (as_list as_string) 
let (get_defensive : Prims.unit -> Prims.string) =
  fun uu____1177  -> lookup_opt "defensive" as_string 
let (get_dep : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1182  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : Prims.unit -> Prims.bool) =
  fun uu____1187  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : Prims.unit -> Prims.bool) =
  fun uu____1190  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : Prims.unit -> Prims.bool) =
  fun uu____1193  -> lookup_opt "doc" as_bool 
let (get_dump_module : Prims.unit -> Prims.string Prims.list) =
  fun uu____1198  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_inference : Prims.unit -> Prims.bool) =
  fun uu____1203  -> lookup_opt "eager_inference" as_bool 
let (get_expose_interfaces : Prims.unit -> Prims.bool) =
  fun uu____1206  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1213  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : Prims.unit -> Prims.string Prims.list) =
  fun uu____1224  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : Prims.unit -> Prims.string Prims.list) =
  fun uu____1231  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : Prims.unit -> Prims.bool) =
  fun uu____1236  -> lookup_opt "fs_typ_app" as_bool 
let (get_fstar_home :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1241  -> lookup_opt "fstar_home" (as_option as_string) 
let (get_hide_uvar_nums : Prims.unit -> Prims.bool) =
  fun uu____1246  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : Prims.unit -> Prims.bool) =
  fun uu____1249  -> lookup_opt "hint_info" as_bool 
let (get_hint_file :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1254  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : Prims.unit -> Prims.bool) =
  fun uu____1259  -> lookup_opt "in" as_bool 
let (get_ide : Prims.unit -> Prims.bool) =
  fun uu____1262  -> lookup_opt "ide" as_bool 
let (get_include : Prims.unit -> Prims.string Prims.list) =
  fun uu____1267  -> lookup_opt "include" (as_list as_string) 
let (get_indent : Prims.unit -> Prims.bool) =
  fun uu____1272  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : Prims.unit -> Prims.int) =
  fun uu____1275  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : Prims.unit -> Prims.int) =
  fun uu____1278  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : Prims.unit -> Prims.bool) =
  fun uu____1281  -> lookup_opt "lax" as_bool 
let (get_load : Prims.unit -> Prims.string Prims.list) =
  fun uu____1286  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : Prims.unit -> Prims.bool) =
  fun uu____1291  -> lookup_opt "log_queries" as_bool 
let (get_log_types : Prims.unit -> Prims.bool) =
  fun uu____1294  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : Prims.unit -> Prims.int) =
  fun uu____1297  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : Prims.unit -> Prims.int) =
  fun uu____1300  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : Prims.unit -> Prims.int) =
  fun uu____1303  -> lookup_opt "min_fuel" as_int 
let (get_MLish : Prims.unit -> Prims.bool) =
  fun uu____1306  -> lookup_opt "MLish" as_bool 
let (get_n_cores : Prims.unit -> Prims.int) =
  fun uu____1309  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : Prims.unit -> Prims.bool) =
  fun uu____1312  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : Prims.unit -> Prims.string Prims.list) =
  fun uu____1317  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : Prims.unit -> Prims.bool) =
  fun uu____1322  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : Prims.unit -> Prims.bool) =
  fun uu____1325  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : Prims.unit -> Prims.bool) =
  fun uu____1328  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1333  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : Prims.unit -> Prims.bool) =
  fun uu____1338  -> lookup_opt "ugly" as_bool 
let (get_prims : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1343  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : Prims.unit -> Prims.bool) =
  fun uu____1348  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : Prims.unit -> Prims.bool) =
  fun uu____1351  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : Prims.unit -> Prims.bool) =
  fun uu____1354  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : Prims.unit -> Prims.bool) =
  fun uu____1357  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : Prims.unit -> Prims.bool) =
  fun uu____1360  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : Prims.unit -> Prims.bool) =
  fun uu____1363  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : Prims.unit -> Prims.bool) =
  fun uu____1366  -> lookup_opt "prn" as_bool 
let (get_query_stats : Prims.unit -> Prims.bool) =
  fun uu____1369  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : Prims.unit -> Prims.bool) =
  fun uu____1372  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1377  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : Prims.unit -> Prims.bool) =
  fun uu____1382  -> lookup_opt "silent" as_bool 
let (get_smt : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1387  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : Prims.unit -> Prims.bool) =
  fun uu____1392  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : Prims.unit -> Prims.string) =
  fun uu____1395  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : Prims.unit -> Prims.string) =
  fun uu____1398  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : Prims.unit -> Prims.bool) =
  fun uu____1401  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : Prims.unit -> Prims.bool) =
  fun uu____1404  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : Prims.unit -> Prims.int) =
  fun uu____1407  -> lookup_opt "tactic_trace_d" as_int 
let (get_timing : Prims.unit -> Prims.bool) =
  fun uu____1410  -> lookup_opt "timing" as_bool 
let (get_trace_error : Prims.unit -> Prims.bool) =
  fun uu____1413  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : Prims.unit -> Prims.bool) =
  fun uu____1416  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : Prims.unit -> Prims.bool) =
  fun uu____1419  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : Prims.unit -> Prims.bool) =
  fun uu____1422  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : Prims.unit -> Prims.bool) =
  fun uu____1425  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : Prims.unit -> Prims.bool) =
  fun uu____1428  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1433  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : Prims.unit -> Prims.bool) =
  fun uu____1438  ->
    let uu____1439 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1439
  
let (get_using_facts_from :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1446  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1457  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : Prims.unit -> Prims.string Prims.list) =
  fun uu____1464  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : Prims.unit -> Prims.string Prims.list) =
  fun uu____1471  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : Prims.unit -> Prims.bool) =
  fun uu____1476  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : Prims.unit -> Prims.bool) =
  fun uu____1479  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : Prims.unit -> Prims.string Prims.list) =
  fun uu____1484  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : Prims.unit -> Prims.bool) =
  fun uu____1489  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : Prims.unit -> Prims.int) =
  fun uu____1492  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : Prims.unit -> Prims.int) =
  fun uu____1495  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : Prims.unit -> Prims.int) =
  fun uu____1498  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : Prims.unit -> Prims.bool) =
  fun uu____1501  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : Prims.unit -> Prims.bool) =
  fun uu____1504  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : Prims.unit -> Prims.bool) =
  fun uu____1507  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : Prims.unit -> Prims.string) =
  fun uu____1510  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : Prims.unit -> Prims.bool) =
  fun uu____1513  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___43_1516  ->
    match uu___43_1516 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1524 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1528 = get_debug_level ()  in
    FStar_All.pipe_right uu____1528
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : Prims.unit -> Prims.unit) =
  fun uu____1659  ->
    let uu____1660 =
      let uu____1661 = FStar_ST.op_Bang _version  in
      let uu____1681 = FStar_ST.op_Bang _platform  in
      let uu____1701 = FStar_ST.op_Bang _compiler  in
      let uu____1721 = FStar_ST.op_Bang _date  in
      let uu____1741 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1661
        uu____1681 uu____1701 uu____1721 uu____1741
       in
    FStar_Util.print_string uu____1660
  
let display_usage_aux :
  'Auu____1764 'Auu____1765 .
    ('Auu____1764,Prims.string,'Auu____1765 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____1812  ->
         match uu____1812 with
         | (uu____1823,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____1834 =
                      let uu____1835 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____1835  in
                    FStar_Util.print_string uu____1834
                  else
                    (let uu____1837 =
                       let uu____1838 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____1838 doc  in
                     FStar_Util.print_string uu____1837)
              | FStar_Getopt.OneArg (uu____1839,argname) ->
                  if doc = ""
                  then
                    let uu____1845 =
                      let uu____1846 = FStar_Util.colorize_bold flag  in
                      let uu____1847 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____1846 uu____1847
                       in
                    FStar_Util.print_string uu____1845
                  else
                    (let uu____1849 =
                       let uu____1850 = FStar_Util.colorize_bold flag  in
                       let uu____1851 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____1850
                         uu____1851 doc
                        in
                     FStar_Util.print_string uu____1849))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____1875 = o  in
    match uu____1875 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____1905 =
                let uu____1906 = f ()  in set_option name uu____1906  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____1917 = f x  in set_option name uu____1917
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____1931 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____1931  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____1950 =
        let uu____1953 = lookup_opt name as_list'  in
        FStar_List.append uu____1953 [value]  in
      mk_list uu____1950
  
let accumulate_string :
  'Auu____1962 .
    Prims.string ->
      ('Auu____1962 -> Prims.string) -> 'Auu____1962 -> Prims.unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____1980 =
          let uu____1981 =
            let uu____1982 = post_processor value  in mk_string uu____1982
             in
          accumulated_option name uu____1981  in
        set_option name uu____1980
  
let (add_extract_module : Prims.string -> Prims.unit) =
  fun s  -> accumulate_string "extract_module" FStar_String.lowercase s 
let (add_extract_namespace : Prims.string -> Prims.unit) =
  fun s  -> accumulate_string "extract_namespace" FStar_String.lowercase s 
let (add_verify_module : Prims.string -> Prims.unit) =
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
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Const : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____2060 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2072 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2083 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2088 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2100 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2114 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2138 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2174 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2204 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2216 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2234 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type ->
    (Prims.unit -> Prims.unit,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2266 -> true
    | uu____2267 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2274 -> uu____2274
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2288 ->
              let uu____2289 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2289 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2293 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2293
          | PathStr uu____2296 -> mk_path str_val
          | SimpleStr uu____2297 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2302 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2315 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2315
          | Accumulated elem_spec ->
              let v1 = parse_opt_val opt_name elem_spec str_val  in
              accumulated_option opt_name v1
          | ReverseAccumulated elem_spec ->
              let v1 = parse_opt_val opt_name elem_spec str_val  in
              reverse_accumulated_option opt_name v1
          | WithSideEffect (side_effect,elem_spec) ->
              (side_effect (); parse_opt_val opt_name elem_spec str_val)
        with
        | InvalidArgument opt_name1 ->
            let uu____2332 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2332
  
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ  ->
    let desc_of_enum cases =
      FStar_Pervasives_Native.Some
        (Prims.strcat "[" (Prims.strcat (FStar_String.concat "|" cases) "]"))
       in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____2365,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2373,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2392 = desc_of_opt_type typ  in
      match uu____2392 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2398  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2410 =
      let uu____2411 = as_string s  in FStar_String.lowercase uu____2411  in
    mk_string uu____2410
  
let rec (specs_with_types :
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2428  ->
    let uu____2439 =
      let uu____2450 =
        let uu____2461 =
          let uu____2470 = let uu____2471 = mk_bool true  in Const uu____2471
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2470,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
           in
        let uu____2472 =
          let uu____2483 =
            let uu____2494 =
              let uu____2505 =
                let uu____2516 =
                  let uu____2527 =
                    let uu____2538 =
                      let uu____2549 =
                        let uu____2560 =
                          let uu____2569 =
                            let uu____2570 = mk_bool true  in
                            Const uu____2570  in
                          (FStar_Getopt.noshort, "detail_errors", uu____2569,
                            "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                           in
                        let uu____2571 =
                          let uu____2582 =
                            let uu____2591 =
                              let uu____2592 = mk_bool true  in
                              Const uu____2592  in
                            (FStar_Getopt.noshort, "detail_hint_replay",
                              uu____2591,
                              "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                             in
                          let uu____2593 =
                            let uu____2604 =
                              let uu____2613 =
                                let uu____2614 = mk_bool true  in
                                Const uu____2614  in
                              (FStar_Getopt.noshort, "doc", uu____2613,
                                "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                               in
                            let uu____2615 =
                              let uu____2626 =
                                let uu____2637 =
                                  let uu____2646 =
                                    let uu____2647 = mk_bool true  in
                                    Const uu____2647  in
                                  (FStar_Getopt.noshort, "eager_inference",
                                    uu____2646,
                                    "Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                   in
                                let uu____2648 =
                                  let uu____2659 =
                                    let uu____2670 =
                                      let uu____2681 =
                                        let uu____2692 =
                                          let uu____2701 =
                                            let uu____2702 = mk_bool true  in
                                            Const uu____2702  in
                                          (FStar_Getopt.noshort,
                                            "expose_interfaces", uu____2701,
                                            "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                           in
                                        let uu____2703 =
                                          let uu____2714 =
                                            let uu____2725 =
                                              let uu____2734 =
                                                let uu____2735 = mk_bool true
                                                   in
                                                Const uu____2735  in
                                              (FStar_Getopt.noshort,
                                                "hide_uvar_nums", uu____2734,
                                                "Don't print unification variable numbers")
                                               in
                                            let uu____2736 =
                                              let uu____2747 =
                                                let uu____2758 =
                                                  let uu____2767 =
                                                    let uu____2768 =
                                                      mk_bool true  in
                                                    Const uu____2768  in
                                                  (FStar_Getopt.noshort,
                                                    "hint_info", uu____2767,
                                                    "Print information regarding hints (deprecated; use --query_stats instead)")
                                                   in
                                                let uu____2769 =
                                                  let uu____2780 =
                                                    let uu____2789 =
                                                      let uu____2790 =
                                                        mk_bool true  in
                                                      Const uu____2790  in
                                                    (FStar_Getopt.noshort,
                                                      "in", uu____2789,
                                                      "Legacy interactive mode; reads input from stdin")
                                                     in
                                                  let uu____2791 =
                                                    let uu____2802 =
                                                      let uu____2811 =
                                                        let uu____2812 =
                                                          mk_bool true  in
                                                        Const uu____2812  in
                                                      (FStar_Getopt.noshort,
                                                        "ide", uu____2811,
                                                        "JSON-based interactive mode for IDEs")
                                                       in
                                                    let uu____2813 =
                                                      let uu____2824 =
                                                        let uu____2835 =
                                                          let uu____2844 =
                                                            let uu____2845 =
                                                              mk_bool true
                                                               in
                                                            Const uu____2845
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "indent",
                                                            uu____2844,
                                                            "Parses and outputs the files on the command line")
                                                           in
                                                        let uu____2846 =
                                                          let uu____2857 =
                                                            let uu____2868 =
                                                              let uu____2879
                                                                =
                                                                let uu____2888
                                                                  =
                                                                  let uu____2889
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                  Const
                                                                    uu____2889
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "lax",
                                                                  uu____2888,
                                                                  "Run the lax-type checker only (admit all verification conditions)")
                                                                 in
                                                              let uu____2890
                                                                =
                                                                let uu____2901
                                                                  =
                                                                  let uu____2912
                                                                    =
                                                                    let uu____2921
                                                                    =
                                                                    let uu____2922
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____2922
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____2921,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                  let uu____2923
                                                                    =
                                                                    let uu____2934
                                                                    =
                                                                    let uu____2943
                                                                    =
                                                                    let uu____2944
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____2944
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____2943,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____2945
                                                                    =
                                                                    let uu____2956
                                                                    =
                                                                    let uu____2967
                                                                    =
                                                                    let uu____2978
                                                                    =
                                                                    let uu____2989
                                                                    =
                                                                    let uu____2998
                                                                    =
                                                                    let uu____2999
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____2999
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____2998,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3000
                                                                    =
                                                                    let uu____3011
                                                                    =
                                                                    let uu____3022
                                                                    =
                                                                    let uu____3031
                                                                    =
                                                                    let uu____3032
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3032
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3031,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3033
                                                                    =
                                                                    let uu____3044
                                                                    =
                                                                    let uu____3055
                                                                    =
                                                                    let uu____3064
                                                                    =
                                                                    let uu____3065
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3065
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3064,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3066
                                                                    =
                                                                    let uu____3077
                                                                    =
                                                                    let uu____3086
                                                                    =
                                                                    let uu____3087
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3087
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3086,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3088
                                                                    =
                                                                    let uu____3099
                                                                    =
                                                                    let uu____3108
                                                                    =
                                                                    let uu____3109
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3109
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3108,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3110
                                                                    =
                                                                    let uu____3121
                                                                    =
                                                                    let uu____3132
                                                                    =
                                                                    let uu____3143
                                                                    =
                                                                    let uu____3152
                                                                    =
                                                                    let uu____3153
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3153
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3152,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3154
                                                                    =
                                                                    let uu____3165
                                                                    =
                                                                    let uu____3174
                                                                    =
                                                                    let uu____3175
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3175
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3174,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3176
                                                                    =
                                                                    let uu____3187
                                                                    =
                                                                    let uu____3196
                                                                    =
                                                                    let uu____3197
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3197
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3196,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3198
                                                                    =
                                                                    let uu____3209
                                                                    =
                                                                    let uu____3218
                                                                    =
                                                                    let uu____3219
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3219
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3218,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3220
                                                                    =
                                                                    let uu____3231
                                                                    =
                                                                    let uu____3240
                                                                    =
                                                                    let uu____3241
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3241
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3240,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3242
                                                                    =
                                                                    let uu____3253
                                                                    =
                                                                    let uu____3262
                                                                    =
                                                                    let uu____3263
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3263
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3262,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3264
                                                                    =
                                                                    let uu____3275
                                                                    =
                                                                    let uu____3284
                                                                    =
                                                                    let uu____3285
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3285
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3284,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3286
                                                                    =
                                                                    let uu____3297
                                                                    =
                                                                    let uu____3306
                                                                    =
                                                                    let uu____3307
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3307
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3306,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3308
                                                                    =
                                                                    let uu____3319
                                                                    =
                                                                    let uu____3328
                                                                    =
                                                                    let uu____3329
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3329
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3328,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3330
                                                                    =
                                                                    let uu____3341
                                                                    =
                                                                    let uu____3352
                                                                    =
                                                                    let uu____3361
                                                                    =
                                                                    let uu____3362
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3362
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3361,
                                                                    " ")  in
                                                                    let uu____3363
                                                                    =
                                                                    let uu____3374
                                                                    =
                                                                    let uu____3385
                                                                    =
                                                                    let uu____3396
                                                                    =
                                                                    let uu____3407
                                                                    =
                                                                    let uu____3418
                                                                    =
                                                                    let uu____3427
                                                                    =
                                                                    let uu____3428
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3428
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____3427,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____3429
                                                                    =
                                                                    let uu____3440
                                                                    =
                                                                    let uu____3449
                                                                    =
                                                                    let uu____3450
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3450
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3449,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____3451
                                                                    =
                                                                    let uu____3462
                                                                    =
                                                                    let uu____3473
                                                                    =
                                                                    let uu____3482
                                                                    =
                                                                    let uu____3483
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3483
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3482,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____3484
                                                                    =
                                                                    let uu____3495
                                                                    =
                                                                    let uu____3504
                                                                    =
                                                                    let uu____3505
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3505
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3504,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____3506
                                                                    =
                                                                    let uu____3517
                                                                    =
                                                                    let uu____3526
                                                                    =
                                                                    let uu____3527
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3527
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3526,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____3528
                                                                    =
                                                                    let uu____3539
                                                                    =
                                                                    let uu____3548
                                                                    =
                                                                    let uu____3549
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3549
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____3548,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____3550
                                                                    =
                                                                    let uu____3561
                                                                    =
                                                                    let uu____3570
                                                                    =
                                                                    let uu____3571
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3571
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____3570,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____3572
                                                                    =
                                                                    let uu____3583
                                                                    =
                                                                    let uu____3592
                                                                    =
                                                                    let uu____3593
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3593
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____3592,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____3594
                                                                    =
                                                                    let uu____3605
                                                                    =
                                                                    let uu____3614
                                                                    =
                                                                    let uu____3615
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3615
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____3614,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____3616
                                                                    =
                                                                    let uu____3627
                                                                    =
                                                                    let uu____3636
                                                                    =
                                                                    let uu____3637
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3637
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____3636,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____3638
                                                                    =
                                                                    let uu____3649
                                                                    =
                                                                    let uu____3660
                                                                    =
                                                                    let uu____3669
                                                                    =
                                                                    let uu____3670
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3670
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____3669,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____3671
                                                                    =
                                                                    let uu____3682
                                                                    =
                                                                    let uu____3693
                                                                    =
                                                                    let uu____3704
                                                                    =
                                                                    let uu____3715
                                                                    =
                                                                    let uu____3724
                                                                    =
                                                                    let uu____3725
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3725
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____3724,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____3726
                                                                    =
                                                                    let uu____3737
                                                                    =
                                                                    let uu____3747
                                                                    =
                                                                    let uu____3748
                                                                    =
                                                                    let uu____3755
                                                                    =
                                                                    let uu____3756
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3756
                                                                     in
                                                                    ((fun
                                                                    uu____3761
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____3755)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____3748
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____3747,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____3765
                                                                    =
                                                                    let uu____3777
                                                                    =
                                                                    let uu____3786
                                                                    =
                                                                    let uu____3787
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3787
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____3786,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____3788
                                                                    =
                                                                    let uu____3799
                                                                    =
                                                                    let uu____3810
                                                                    =
                                                                    let uu____3819
                                                                    =
                                                                    let uu____3820
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3820
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____3819,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____3821
                                                                    =
                                                                    let uu____3832
                                                                    =
                                                                    let uu____3843
                                                                    =
                                                                    let uu____3854
                                                                    =
                                                                    let uu____3865
                                                                    =
                                                                    let uu____3876
                                                                    =
                                                                    let uu____3885
                                                                    =
                                                                    let uu____3886
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3886
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____3885,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____3887
                                                                    =
                                                                    let uu____3898
                                                                    =
                                                                    let uu____3907
                                                                    =
                                                                    let uu____3908
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3908
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____3907,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____3909
                                                                    =
                                                                    let uu____3920
                                                                    =
                                                                    let uu____3931
                                                                    =
                                                                    let uu____3940
                                                                    =
                                                                    let uu____3941
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3941
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    uu____3940,
                                                                    "Extract interfaces from the dependencies and use them for verification")
                                                                     in
                                                                    let uu____3942
                                                                    =
                                                                    let uu____3953
                                                                    =
                                                                    let uu____3963
                                                                    =
                                                                    let uu____3964
                                                                    =
                                                                    let uu____3971
                                                                    =
                                                                    let uu____3972
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3972
                                                                     in
                                                                    ((fun
                                                                    uu____3977
                                                                     ->
                                                                    (
                                                                    let uu____3979
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____3979);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____3971)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____3964
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____3963,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____3953]
                                                                     in
                                                                    uu____3931
                                                                    ::
                                                                    uu____3942
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____3920
                                                                     in
                                                                    uu____3898
                                                                    ::
                                                                    uu____3909
                                                                     in
                                                                    uu____3876
                                                                    ::
                                                                    uu____3887
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'false')")
                                                                    ::
                                                                    uu____3865
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____3854
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____3843
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____3832
                                                                     in
                                                                    uu____3810
                                                                    ::
                                                                    uu____3821
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____3799
                                                                     in
                                                                    uu____3777
                                                                    ::
                                                                    uu____3788
                                                                     in
                                                                    uu____3737
                                                                    ::
                                                                    uu____3765
                                                                     in
                                                                    uu____3715
                                                                    ::
                                                                    uu____3726
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____3704
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____3693
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____3682
                                                                     in
                                                                    uu____3660
                                                                    ::
                                                                    uu____3671
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____3649
                                                                     in
                                                                    uu____3627
                                                                    ::
                                                                    uu____3638
                                                                     in
                                                                    uu____3605
                                                                    ::
                                                                    uu____3616
                                                                     in
                                                                    uu____3583
                                                                    ::
                                                                    uu____3594
                                                                     in
                                                                    uu____3561
                                                                    ::
                                                                    uu____3572
                                                                     in
                                                                    uu____3539
                                                                    ::
                                                                    uu____3550
                                                                     in
                                                                    uu____3517
                                                                    ::
                                                                    uu____3528
                                                                     in
                                                                    uu____3495
                                                                    ::
                                                                    uu____3506
                                                                     in
                                                                    uu____3473
                                                                    ::
                                                                    uu____3484
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3462
                                                                     in
                                                                    uu____3440
                                                                    ::
                                                                    uu____3451
                                                                     in
                                                                    uu____3418
                                                                    ::
                                                                    uu____3429
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3407
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3396
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3385
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3374
                                                                     in
                                                                    uu____3352
                                                                    ::
                                                                    uu____3363
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3341
                                                                     in
                                                                    uu____3319
                                                                    ::
                                                                    uu____3330
                                                                     in
                                                                    uu____3297
                                                                    ::
                                                                    uu____3308
                                                                     in
                                                                    uu____3275
                                                                    ::
                                                                    uu____3286
                                                                     in
                                                                    uu____3253
                                                                    ::
                                                                    uu____3264
                                                                     in
                                                                    uu____3231
                                                                    ::
                                                                    uu____3242
                                                                     in
                                                                    uu____3209
                                                                    ::
                                                                    uu____3220
                                                                     in
                                                                    uu____3187
                                                                    ::
                                                                    uu____3198
                                                                     in
                                                                    uu____3165
                                                                    ::
                                                                    uu____3176
                                                                     in
                                                                    uu____3143
                                                                    ::
                                                                    uu____3154
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3132
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3121
                                                                     in
                                                                    uu____3099
                                                                    ::
                                                                    uu____3110
                                                                     in
                                                                    uu____3077
                                                                    ::
                                                                    uu____3088
                                                                     in
                                                                    uu____3055
                                                                    ::
                                                                    uu____3066
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3044
                                                                     in
                                                                    uu____3022
                                                                    ::
                                                                    uu____3033
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3011
                                                                     in
                                                                    uu____2989
                                                                    ::
                                                                    uu____3000
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____2978
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____2967
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____2956
                                                                     in
                                                                    uu____2934
                                                                    ::
                                                                    uu____2945
                                                                     in
                                                                  uu____2912
                                                                    ::
                                                                    uu____2923
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "load",
                                                                  (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                  "Load compiled module")
                                                                  ::
                                                                  uu____2901
                                                                 in
                                                              uu____2879 ::
                                                                uu____2890
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "initial_ifuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                              :: uu____2868
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "initial_fuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of recursive functions to try initially (default 2)")
                                                            :: uu____2857
                                                           in
                                                        uu____2835 ::
                                                          uu____2846
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "include",
                                                        (ReverseAccumulated
                                                           (PathStr "path")),
                                                        "A directory in which to search for files included on the command line")
                                                        :: uu____2824
                                                       in
                                                    uu____2802 :: uu____2813
                                                     in
                                                  uu____2780 :: uu____2791
                                                   in
                                                uu____2758 :: uu____2769  in
                                              (FStar_Getopt.noshort,
                                                "hint_file",
                                                (PathStr "path"),
                                                "Read/write hints to <path> (instead of module-specific hints files)")
                                                :: uu____2747
                                               in
                                            uu____2725 :: uu____2736  in
                                          (FStar_Getopt.noshort,
                                            "fstar_home", (PathStr "dir"),
                                            "Set the FSTAR_HOME variable to <dir>")
                                            :: uu____2714
                                           in
                                        uu____2692 :: uu____2703  in
                                      (FStar_Getopt.noshort,
                                        "extract_namespace",
                                        (Accumulated
                                           (PostProcessed
                                              (pp_lowercase,
                                                (SimpleStr "namespace name")))),
                                        "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                        :: uu____2681
                                       in
                                    (FStar_Getopt.noshort, "extract_module",
                                      (Accumulated
                                         (PostProcessed
                                            (pp_lowercase,
                                              (SimpleStr "module_name")))),
                                      "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                      :: uu____2670
                                     in
                                  (FStar_Getopt.noshort, "extract",
                                    (Accumulated
                                       (SimpleStr
                                          "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                    "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                    :: uu____2659
                                   in
                                uu____2637 :: uu____2648  in
                              (FStar_Getopt.noshort, "dump_module",
                                (Accumulated (SimpleStr "module_name")), "")
                                :: uu____2626
                               in
                            uu____2604 :: uu____2615  in
                          uu____2582 :: uu____2593  in
                        uu____2560 :: uu____2571  in
                      (FStar_Getopt.noshort, "dep",
                        (EnumStr ["make"; "graph"; "full"]),
                        "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                        :: uu____2549
                       in
                    (FStar_Getopt.noshort, "defensive",
                      (EnumStr ["no"; "warn"; "fail"]),
                      "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                      :: uu____2538
                     in
                  (FStar_Getopt.noshort, "debug_level",
                    (Accumulated
                       (OpenEnumStr
                          (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                    "Control the verbosity of debugging info") :: uu____2527
                   in
                (FStar_Getopt.noshort, "debug",
                  (Accumulated (SimpleStr "module_name")),
                  "Print lots of debugging information while checking module")
                  :: uu____2516
                 in
              (FStar_Getopt.noshort, "codegen-lib",
                (Accumulated (SimpleStr "namespace")),
                "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                :: uu____2505
               in
            (FStar_Getopt.noshort, "codegen",
              (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
              "Generate code for further compilation to executable code, or build a compiler plugin")
              :: uu____2494
             in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2483
           in
        uu____2461 :: uu____2472  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2450
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2439

and (specs : Prims.unit -> FStar_Getopt.opt Prims.list) =
  fun uu____4735  ->
    let uu____4738 = specs_with_types ()  in
    FStar_List.map
      (fun uu____4763  ->
         match uu____4763 with
         | (short,long,typ,doc) ->
             let uu____4776 =
               let uu____4787 = arg_spec_of_opt_type long typ  in
               (short, long, uu____4787, doc)  in
             mk_spec uu____4776) uu____4738

let (settable : Prims.string -> Prims.bool) =
  fun uu___44_4794  ->
    match uu___44_4794 with
    | "admit_smt_queries" -> true
    | "admit_except" -> true
    | "debug" -> true
    | "debug_level" -> true
    | "defensive" -> true
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
    | "no_smt" -> true
    | "__no_positivity" -> true
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
    | "normalize_pure_terms_for_extraction" -> true
    | "tactic_raw_binders" -> true
    | "tactic_trace" -> true
    | "tactic_trace_d" -> true
    | "__temp_fast_implicits" -> true
    | "__temp_no_proj" -> true
    | "reuse_hint_for" -> true
    | "warn_error" -> true
    | "z3rlimit_factor" -> true
    | "z3rlimit" -> true
    | "z3refresh" -> true
    | "use_two_phase_tc" -> true
    | "vcgen.optimize_bind_as_seq" -> true
    | uu____4795 -> false
  
let (resettable : Prims.string -> Prims.bool) =
  fun s  ->
    (((settable s) || (s = "z3seed")) || (s = "z3cliopt")) ||
      (s = "using_facts_from")
  
let (all_specs : FStar_Getopt.opt Prims.list) = specs () 
let (all_specs_with_types :
  (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  = specs_with_types () 
let (settable_specs :
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____4852  ->
          match uu____4852 with
          | (uu____4863,x,uu____4865,uu____4866) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____4912  ->
          match uu____4912 with
          | (uu____4923,x,uu____4925,uu____4926) -> resettable x))
  
let (display_usage : Prims.unit -> Prims.unit) =
  fun uu____4933  ->
    let uu____4934 = specs ()  in display_usage_aux uu____4934
  
let (fstar_home : Prims.unit -> Prims.string) =
  fun uu____4949  ->
    let uu____4950 = get_fstar_home ()  in
    match uu____4950 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir ()  in
        let x1 = Prims.strcat x "/.."  in
        ((let uu____4956 =
            let uu____4961 = mk_string x1  in ("fstar_home", uu____4961)  in
          set_option' uu____4956);
         x1)
    | FStar_Pervasives_Native.Some x -> x
  
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____4969 -> true
    | uu____4970 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____4977 -> uu____4977
  
let (set_options : options -> Prims.string -> FStar_Getopt.parse_cmdline_res)
  =
  fun o  ->
    fun s  ->
      let specs1 =
        match o with
        | Set  -> settable_specs
        | Reset  -> resettable_specs
        | Restore  -> all_specs  in
      try
        if s = ""
        then FStar_Getopt.Success
        else
          FStar_Getopt.parse_string specs1
            (fun s1  -> FStar_Exn.raise (File_argument s1)) s
      with
      | File_argument s1 ->
          let uu____5021 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5021
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5047  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5052 =
             let uu____5055 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5055 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5052)
       in
    let uu____5104 =
      let uu____5107 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5107
       in
    (res, uu____5104)
  
let (file_list : Prims.unit -> Prims.string Prims.list) =
  fun uu____5139  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____5172 = specs ()  in
       FStar_Getopt.parse_cmdline uu____5172 (fun x  -> ())  in
     (let uu____5178 =
        let uu____5183 =
          let uu____5184 = FStar_List.map mk_string old_verify_module  in
          List uu____5184  in
        ("verify_module", uu____5183)  in
      set_option' uu____5178);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____5192 =
        let uu____5193 =
          let uu____5194 =
            let uu____5195 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____5195  in
          (FStar_String.length f1) - uu____5194  in
        uu____5193 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5192  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5199 = get_lax ()  in
    if uu____5199
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____5207 = module_name_of_file_name fn  in should_verify uu____5207
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5211 = get___temp_no_proj ()  in
    FStar_List.contains m uu____5211
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5217 = should_verify m  in
    if uu____5217 then m <> "Prims" else false
  
let (include_path : Prims.unit -> Prims.string Prims.list) =
  fun uu____5223  ->
    let uu____5224 = get_no_default_includes ()  in
    if uu____5224
    then get_include ()
    else
      (let h = fstar_home ()  in
       let defs = universe_include_path_base_dirs  in
       let uu____5232 =
         let uu____5235 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x))
            in
         FStar_All.pipe_right uu____5235
           (FStar_List.filter FStar_Util.file_exists)
          in
       let uu____5248 =
         let uu____5251 = get_include ()  in
         FStar_List.append uu____5251 ["."]  in
       FStar_List.append uu____5232 uu____5248)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun filename  ->
    let uu____5259 = FStar_Util.is_path_absolute filename  in
    if uu____5259
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5266 =
         let uu____5269 = include_path ()  in FStar_List.rev uu____5269  in
       FStar_Util.find_map uu____5266
         (fun p  ->
            let path =
              if p = "." then filename else FStar_Util.join_paths p filename
               in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
  
let (prims : Prims.unit -> Prims.string) =
  fun uu____5282  ->
    let uu____5283 = get_prims ()  in
    match uu____5283 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____5287 = find_file filename  in
        (match uu____5287 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5291 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____5291)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : Prims.unit -> Prims.string) =
  fun uu____5295  ->
    let uu____5296 = prims ()  in FStar_Util.basename uu____5296
  
let (pervasives : Prims.unit -> Prims.string) =
  fun uu____5299  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____5301 = find_file filename  in
    match uu____5301 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5305 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5305
  
let (pervasives_basename : Prims.unit -> Prims.string) =
  fun uu____5308  ->
    let uu____5309 = pervasives ()  in FStar_Util.basename uu____5309
  
let (pervasives_native_basename : Prims.unit -> Prims.string) =
  fun uu____5312  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____5314 = find_file filename  in
    match uu____5314 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5318 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5318
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____5322 = get_odir ()  in
    match uu____5322 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____5329 = get_cache_dir ()  in
    match uu____5329 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____5333 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____5333
  
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun ns  ->
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if FStar_Util.starts_with s "-"
        then
          (let path =
             let uu____5383 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             FStar_Ident.path_of_text uu____5383  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           let uu____5387 = FStar_Ident.path_of_text s1  in
           (uu____5387, true))
       in
    let uu____5388 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____5388 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____5456 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____5456 (FStar_List.contains s)
  
let (__temp_fast_implicits : Prims.unit -> Prims.bool) =
  fun uu____5463  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : Prims.unit -> Prims.bool) =
  fun uu____5466  -> get_admit_smt_queries () 
let (admit_except :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5471  -> get_admit_except () 
let (cache_checked_modules : Prims.unit -> Prims.bool) =
  fun uu____5474  -> get_cache_checked_modules () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin [@@deriving show]
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____5478 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____5482 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____5486 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____5490 -> false
  
let (codegen : Prims.unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____5495  ->
    let uu____5496 = get_codegen ()  in
    FStar_Util.map_opt uu____5496
      (fun uu___45_5500  ->
         match uu___45_5500 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____5501 -> failwith "Impossible")
  
let (codegen_libs : Prims.unit -> Prims.string Prims.list Prims.list) =
  fun uu____5508  ->
    let uu____5509 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____5509
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : Prims.unit -> Prims.bool) =
  fun uu____5524  -> let uu____5525 = get_debug ()  in uu____5525 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____5533 = get_debug ()  in
    FStar_All.pipe_right uu____5533 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____5546 = get_debug ()  in
       FStar_All.pipe_right uu____5546 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : Prims.unit -> Prims.bool) =
  fun uu____5553  -> let uu____5554 = get_defensive ()  in uu____5554 <> "no" 
let (defensive_fail : Prims.unit -> Prims.bool) =
  fun uu____5557  ->
    let uu____5558 = get_defensive ()  in uu____5558 = "fail"
  
let (dep : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5563  -> get_dep () 
let (detail_errors : Prims.unit -> Prims.bool) =
  fun uu____5566  -> get_detail_errors () 
let (detail_hint_replay : Prims.unit -> Prims.bool) =
  fun uu____5569  -> get_detail_hint_replay () 
let (doc : Prims.unit -> Prims.bool) = fun uu____5572  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____5576 = get_dump_module ()  in
    FStar_All.pipe_right uu____5576 (FStar_List.contains s)
  
let (eager_inference : Prims.unit -> Prims.bool) =
  fun uu____5583  -> get_eager_inference () 
let (expose_interfaces : Prims.unit -> Prims.bool) =
  fun uu____5586  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____5590 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____5590
  
let (full_context_dependency : Prims.unit -> Prims.bool) =
  fun uu____5618  -> true 
let (hide_uvar_nums : Prims.unit -> Prims.bool) =
  fun uu____5621  -> get_hide_uvar_nums () 
let (hint_info : Prims.unit -> Prims.bool) =
  fun uu____5624  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5629  -> get_hint_file () 
let (ide : Prims.unit -> Prims.bool) = fun uu____5632  -> get_ide () 
let (indent : Prims.unit -> Prims.bool) = fun uu____5635  -> get_indent () 
let (initial_fuel : Prims.unit -> Prims.int) =
  fun uu____5638  ->
    let uu____5639 = get_initial_fuel ()  in
    let uu____5640 = get_max_fuel ()  in Prims.min uu____5639 uu____5640
  
let (initial_ifuel : Prims.unit -> Prims.int) =
  fun uu____5643  ->
    let uu____5644 = get_initial_ifuel ()  in
    let uu____5645 = get_max_ifuel ()  in Prims.min uu____5644 uu____5645
  
let (interactive : Prims.unit -> Prims.bool) =
  fun uu____5648  -> (get_in ()) || (get_ide ()) 
let (lax : Prims.unit -> Prims.bool) = fun uu____5651  -> get_lax () 
let (load : Prims.unit -> Prims.string Prims.list) =
  fun uu____5656  -> get_load () 
let (legacy_interactive : Prims.unit -> Prims.bool) =
  fun uu____5659  -> get_in () 
let (log_queries : Prims.unit -> Prims.bool) =
  fun uu____5662  -> get_log_queries () 
let (log_types : Prims.unit -> Prims.bool) =
  fun uu____5665  -> get_log_types () 
let (max_fuel : Prims.unit -> Prims.int) = fun uu____5668  -> get_max_fuel () 
let (max_ifuel : Prims.unit -> Prims.int) =
  fun uu____5671  -> get_max_ifuel () 
let (min_fuel : Prims.unit -> Prims.int) = fun uu____5674  -> get_min_fuel () 
let (ml_ish : Prims.unit -> Prims.bool) = fun uu____5677  -> get_MLish () 
let (set_ml_ish : Prims.unit -> Prims.unit) =
  fun uu____5680  -> set_option "MLish" (Bool true) 
let (n_cores : Prims.unit -> Prims.int) = fun uu____5683  -> get_n_cores () 
let (no_default_includes : Prims.unit -> Prims.bool) =
  fun uu____5686  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____5691 = get_no_extract ()  in
    FStar_All.pipe_right uu____5691
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : Prims.unit -> Prims.bool) =
  fun uu____5700  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : Prims.unit -> Prims.bool) =
  fun uu____5703  -> get_no_location_info () 
let (no_smt : Prims.unit -> Prims.bool) = fun uu____5706  -> get_no_smt () 
let (output_dir : Prims.unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____5711  -> get_odir () 
let (ugly : Prims.unit -> Prims.bool) = fun uu____5714  -> get_ugly () 
let (print_bound_var_types : Prims.unit -> Prims.bool) =
  fun uu____5717  -> get_print_bound_var_types () 
let (print_effect_args : Prims.unit -> Prims.bool) =
  fun uu____5720  -> get_print_effect_args () 
let (print_implicits : Prims.unit -> Prims.bool) =
  fun uu____5723  -> get_print_implicits () 
let (print_real_names : Prims.unit -> Prims.bool) =
  fun uu____5726  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : Prims.unit -> Prims.bool) =
  fun uu____5729  -> get_print_universes () 
let (print_z3_statistics : Prims.unit -> Prims.bool) =
  fun uu____5732  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : Prims.unit -> Prims.bool) =
  fun uu____5735  -> get_query_stats () 
let (record_hints : Prims.unit -> Prims.bool) =
  fun uu____5738  -> get_record_hints () 
let (reuse_hint_for :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5743  -> get_reuse_hint_for () 
let (silent : Prims.unit -> Prims.bool) = fun uu____5746  -> get_silent () 
let (smtencoding_elim_box : Prims.unit -> Prims.bool) =
  fun uu____5749  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : Prims.unit -> Prims.bool) =
  fun uu____5752  ->
    let uu____5753 = get_smtencoding_nl_arith_repr ()  in
    uu____5753 = "native"
  
let (smtencoding_nl_arith_wrapped : Prims.unit -> Prims.bool) =
  fun uu____5756  ->
    let uu____5757 = get_smtencoding_nl_arith_repr ()  in
    uu____5757 = "wrapped"
  
let (smtencoding_nl_arith_default : Prims.unit -> Prims.bool) =
  fun uu____5760  ->
    let uu____5761 = get_smtencoding_nl_arith_repr ()  in
    uu____5761 = "boxwrap"
  
let (smtencoding_l_arith_native : Prims.unit -> Prims.bool) =
  fun uu____5764  ->
    let uu____5765 = get_smtencoding_l_arith_repr ()  in
    uu____5765 = "native"
  
let (smtencoding_l_arith_default : Prims.unit -> Prims.bool) =
  fun uu____5768  ->
    let uu____5769 = get_smtencoding_l_arith_repr ()  in
    uu____5769 = "boxwrap"
  
let (tactic_raw_binders : Prims.unit -> Prims.bool) =
  fun uu____5772  -> get_tactic_raw_binders () 
let (tactic_trace : Prims.unit -> Prims.bool) =
  fun uu____5775  -> get_tactic_trace () 
let (tactic_trace_d : Prims.unit -> Prims.int) =
  fun uu____5778  -> get_tactic_trace_d () 
let (timing : Prims.unit -> Prims.bool) = fun uu____5781  -> get_timing () 
let (trace_error : Prims.unit -> Prims.bool) =
  fun uu____5784  -> get_trace_error () 
let (unthrottle_inductives : Prims.unit -> Prims.bool) =
  fun uu____5787  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : Prims.unit -> Prims.bool) =
  fun uu____5790  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : Prims.unit -> Prims.bool) =
  fun uu____5793  -> get_use_eq_at_higher_order () 
let (use_hints : Prims.unit -> Prims.bool) =
  fun uu____5796  -> get_use_hints () 
let (use_hint_hashes : Prims.unit -> Prims.bool) =
  fun uu____5799  -> get_use_hint_hashes () 
let (use_native_tactics :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5804  -> get_use_native_tactics () 
let (use_tactics : Prims.unit -> Prims.bool) =
  fun uu____5807  -> get_use_tactics () 
let (using_facts_from :
  Prims.unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____5816  ->
    let uu____5817 = get_using_facts_from ()  in
    match uu____5817 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : Prims.unit -> Prims.bool) =
  fun uu____5851  ->
    let uu____5852 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____5852
  
let (vcgen_decorate_with_type : Prims.unit -> Prims.bool) =
  fun uu____5857  ->
    let uu____5858 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____5858 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____5861 -> false
  
let (warn_default_effects : Prims.unit -> Prims.bool) =
  fun uu____5866  -> get_warn_default_effects () 
let (z3_exe : Prims.unit -> Prims.string) =
  fun uu____5869  ->
    let uu____5870 = get_smt ()  in
    match uu____5870 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : Prims.unit -> Prims.string Prims.list) =
  fun uu____5878  -> get_z3cliopt () 
let (z3_refresh : Prims.unit -> Prims.bool) =
  fun uu____5881  -> get_z3refresh () 
let (z3_rlimit : Prims.unit -> Prims.int) =
  fun uu____5884  -> get_z3rlimit () 
let (z3_rlimit_factor : Prims.unit -> Prims.int) =
  fun uu____5887  -> get_z3rlimit_factor () 
let (z3_seed : Prims.unit -> Prims.int) = fun uu____5890  -> get_z3seed () 
let (use_two_phase_tc : Prims.unit -> Prims.bool) =
  fun uu____5893  -> get_use_two_phase_tc () 
let (no_positivity : Prims.unit -> Prims.bool) =
  fun uu____5896  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : Prims.unit -> Prims.bool) =
  fun uu____5899  -> get_ml_no_eta_expand_coertions () 
let (warn_error : Prims.unit -> Prims.string) =
  fun uu____5902  -> get_warn_error () 
let (use_extracted_interfaces : Prims.unit -> Prims.bool) =
  fun uu____5905  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____5910 = get_extract ()  in
    match uu____5910 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____5921 =
            let uu____5934 = get_no_extract ()  in
            let uu____5937 = get_extract_namespace ()  in
            let uu____5940 = get_extract_module ()  in
            (uu____5934, uu____5937, uu____5940)  in
          match uu____5921 with
          | ([],[],[]) -> ()
          | uu____5955 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = FStar_Ident.path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____5997,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____6016 -> false  in
          let uu____6025 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____6059  ->
                    match uu____6059 with
                    | (path,uu____6067) -> matches_path m_components path))
             in
          match uu____6025 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____6078,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____6096 = get_extract_namespace ()  in
          match uu____6096 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____6110 = get_extract_module ()  in
          match uu____6110 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____6122 = no_extract m1  in Prims.op_Negation uu____6122) &&
          (let uu____6124 =
             let uu____6133 = get_extract_namespace ()  in
             let uu____6136 = get_extract_module ()  in
             (uu____6133, uu____6136)  in
           (match uu____6124 with
            | ([],[]) -> true
            | uu____6147 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  