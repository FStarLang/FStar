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
  ("use_extracted_interfaces", (Bool false));
  ("no_reduction_under_match", (Bool false))] 
let (init : Prims.unit -> Prims.unit) =
  fun uu____1033  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : Prims.unit -> Prims.unit) =
  fun uu____1048  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : Prims.unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1107 =
      let uu____1110 = peek ()  in FStar_Util.smap_try_find uu____1110 s  in
    match uu____1107 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1117 . Prims.string -> (option_val -> 'Auu____1117) -> 'Auu____1117
  = fun s  -> fun c  -> c (get_option s) 
let (get_admit_smt_queries : Prims.unit -> Prims.bool) =
  fun uu____1133  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1138  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : Prims.unit -> Prims.bool) =
  fun uu____1143  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1148  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_codegen : Prims.unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1155  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : Prims.unit -> Prims.string Prims.list) =
  fun uu____1162  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : Prims.unit -> Prims.string Prims.list) =
  fun uu____1169  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : Prims.unit -> Prims.string Prims.list) =
  fun uu____1176  -> lookup_opt "debug_level" (as_list as_string) 
let (get_defensive : Prims.unit -> Prims.string) =
  fun uu____1181  -> lookup_opt "defensive" as_string 
let (get_dep : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1186  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : Prims.unit -> Prims.bool) =
  fun uu____1191  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : Prims.unit -> Prims.bool) =
  fun uu____1194  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : Prims.unit -> Prims.bool) =
  fun uu____1197  -> lookup_opt "doc" as_bool 
let (get_dump_module : Prims.unit -> Prims.string Prims.list) =
  fun uu____1202  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_inference : Prims.unit -> Prims.bool) =
  fun uu____1207  -> lookup_opt "eager_inference" as_bool 
let (get_expose_interfaces : Prims.unit -> Prims.bool) =
  fun uu____1210  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1217  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : Prims.unit -> Prims.string Prims.list) =
  fun uu____1228  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : Prims.unit -> Prims.string Prims.list) =
  fun uu____1235  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : Prims.unit -> Prims.bool) =
  fun uu____1240  -> lookup_opt "fs_typ_app" as_bool 
let (get_fstar_home :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1245  -> lookup_opt "fstar_home" (as_option as_string) 
let (get_hide_uvar_nums : Prims.unit -> Prims.bool) =
  fun uu____1250  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : Prims.unit -> Prims.bool) =
  fun uu____1253  -> lookup_opt "hint_info" as_bool 
let (get_hint_file :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1258  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : Prims.unit -> Prims.bool) =
  fun uu____1263  -> lookup_opt "in" as_bool 
let (get_ide : Prims.unit -> Prims.bool) =
  fun uu____1266  -> lookup_opt "ide" as_bool 
let (get_include : Prims.unit -> Prims.string Prims.list) =
  fun uu____1271  -> lookup_opt "include" (as_list as_string) 
let (get_indent : Prims.unit -> Prims.bool) =
  fun uu____1276  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : Prims.unit -> Prims.int) =
  fun uu____1279  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : Prims.unit -> Prims.int) =
  fun uu____1282  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : Prims.unit -> Prims.bool) =
  fun uu____1285  -> lookup_opt "lax" as_bool 
let (get_load : Prims.unit -> Prims.string Prims.list) =
  fun uu____1290  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : Prims.unit -> Prims.bool) =
  fun uu____1295  -> lookup_opt "log_queries" as_bool 
let (get_log_types : Prims.unit -> Prims.bool) =
  fun uu____1298  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : Prims.unit -> Prims.int) =
  fun uu____1301  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : Prims.unit -> Prims.int) =
  fun uu____1304  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : Prims.unit -> Prims.int) =
  fun uu____1307  -> lookup_opt "min_fuel" as_int 
let (get_MLish : Prims.unit -> Prims.bool) =
  fun uu____1310  -> lookup_opt "MLish" as_bool 
let (get_n_cores : Prims.unit -> Prims.int) =
  fun uu____1313  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : Prims.unit -> Prims.bool) =
  fun uu____1316  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : Prims.unit -> Prims.string Prims.list) =
  fun uu____1321  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : Prims.unit -> Prims.bool) =
  fun uu____1326  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : Prims.unit -> Prims.bool) =
  fun uu____1329  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : Prims.unit -> Prims.bool) =
  fun uu____1332  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1337  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : Prims.unit -> Prims.bool) =
  fun uu____1342  -> lookup_opt "ugly" as_bool 
let (get_prims : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1347  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : Prims.unit -> Prims.bool) =
  fun uu____1352  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : Prims.unit -> Prims.bool) =
  fun uu____1355  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : Prims.unit -> Prims.bool) =
  fun uu____1358  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : Prims.unit -> Prims.bool) =
  fun uu____1361  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : Prims.unit -> Prims.bool) =
  fun uu____1364  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : Prims.unit -> Prims.bool) =
  fun uu____1367  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : Prims.unit -> Prims.bool) =
  fun uu____1370  -> lookup_opt "prn" as_bool 
let (get_query_stats : Prims.unit -> Prims.bool) =
  fun uu____1373  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : Prims.unit -> Prims.bool) =
  fun uu____1376  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1381  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : Prims.unit -> Prims.bool) =
  fun uu____1386  -> lookup_opt "silent" as_bool 
let (get_smt : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1391  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : Prims.unit -> Prims.bool) =
  fun uu____1396  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : Prims.unit -> Prims.string) =
  fun uu____1399  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : Prims.unit -> Prims.string) =
  fun uu____1402  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : Prims.unit -> Prims.bool) =
  fun uu____1405  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : Prims.unit -> Prims.bool) =
  fun uu____1408  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : Prims.unit -> Prims.int) =
  fun uu____1411  -> lookup_opt "tactic_trace_d" as_int 
let (get_timing : Prims.unit -> Prims.bool) =
  fun uu____1414  -> lookup_opt "timing" as_bool 
let (get_trace_error : Prims.unit -> Prims.bool) =
  fun uu____1417  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : Prims.unit -> Prims.bool) =
  fun uu____1420  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : Prims.unit -> Prims.bool) =
  fun uu____1423  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : Prims.unit -> Prims.bool) =
  fun uu____1426  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : Prims.unit -> Prims.bool) =
  fun uu____1429  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : Prims.unit -> Prims.bool) =
  fun uu____1432  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1437  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : Prims.unit -> Prims.bool) =
  fun uu____1442  ->
    let uu____1443 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1443
  
let (get_using_facts_from :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1450  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1461  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : Prims.unit -> Prims.string Prims.list) =
  fun uu____1468  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : Prims.unit -> Prims.string Prims.list) =
  fun uu____1475  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : Prims.unit -> Prims.bool) =
  fun uu____1480  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : Prims.unit -> Prims.bool) =
  fun uu____1483  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : Prims.unit -> Prims.string Prims.list) =
  fun uu____1488  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : Prims.unit -> Prims.bool) =
  fun uu____1493  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : Prims.unit -> Prims.int) =
  fun uu____1496  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : Prims.unit -> Prims.int) =
  fun uu____1499  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : Prims.unit -> Prims.int) =
  fun uu____1502  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : Prims.unit -> Prims.bool) =
  fun uu____1505  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : Prims.unit -> Prims.bool) =
  fun uu____1508  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : Prims.unit -> Prims.bool) =
  fun uu____1511  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : Prims.unit -> Prims.string) =
  fun uu____1514  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : Prims.unit -> Prims.bool) =
  fun uu____1517  -> lookup_opt "use_extracted_interfaces" as_bool 
let (no_reduction_under_match : Prims.unit -> Prims.bool) =
  fun uu____1520  -> lookup_opt "no_reduction_under_match" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___43_1523  ->
    match uu___43_1523 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1531 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1535 = get_debug_level ()  in
    FStar_All.pipe_right uu____1535
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : Prims.unit -> Prims.unit) =
  fun uu____1666  ->
    let uu____1667 =
      let uu____1668 = FStar_ST.op_Bang _version  in
      let uu____1688 = FStar_ST.op_Bang _platform  in
      let uu____1708 = FStar_ST.op_Bang _compiler  in
      let uu____1728 = FStar_ST.op_Bang _date  in
      let uu____1748 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1668
        uu____1688 uu____1708 uu____1728 uu____1748
       in
    FStar_Util.print_string uu____1667
  
let display_usage_aux :
  'Auu____1771 'Auu____1772 .
    ('Auu____1771,Prims.string,'Auu____1772 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____1819  ->
         match uu____1819 with
         | (uu____1830,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____1841 =
                      let uu____1842 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____1842  in
                    FStar_Util.print_string uu____1841
                  else
                    (let uu____1844 =
                       let uu____1845 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____1845 doc  in
                     FStar_Util.print_string uu____1844)
              | FStar_Getopt.OneArg (uu____1846,argname) ->
                  if doc = ""
                  then
                    let uu____1852 =
                      let uu____1853 = FStar_Util.colorize_bold flag  in
                      let uu____1854 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____1853 uu____1854
                       in
                    FStar_Util.print_string uu____1852
                  else
                    (let uu____1856 =
                       let uu____1857 = FStar_Util.colorize_bold flag  in
                       let uu____1858 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____1857
                         uu____1858 doc
                        in
                     FStar_Util.print_string uu____1856))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____1882 = o  in
    match uu____1882 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____1912 =
                let uu____1913 = f ()  in set_option name uu____1913  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____1924 = f x  in set_option name uu____1924
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____1938 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____1938  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____1957 =
        let uu____1960 = lookup_opt name as_list'  in
        FStar_List.append uu____1960 [value]  in
      mk_list uu____1957
  
let accumulate_string :
  'Auu____1969 .
    Prims.string ->
      ('Auu____1969 -> Prims.string) -> 'Auu____1969 -> Prims.unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____1987 =
          let uu____1988 =
            let uu____1989 = post_processor value  in mk_string uu____1989
             in
          accumulated_option name uu____1988  in
        set_option name uu____1987
  
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
    match projectee with | Const _0 -> true | uu____2067 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2079 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2090 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2095 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2107 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2121 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2145 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2181 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2211 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2223 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2241 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type ->
    (Prims.unit -> Prims.unit,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2273 -> true
    | uu____2274 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2281 -> uu____2281
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2295 ->
              let uu____2296 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2296 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2300 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2300
          | PathStr uu____2303 -> mk_path str_val
          | SimpleStr uu____2304 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2309 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2322 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2322
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
            let uu____2339 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2339
  
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
    | PostProcessed (uu____2372,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2380,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2399 = desc_of_opt_type typ  in
      match uu____2399 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2405  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2417 =
      let uu____2418 = as_string s  in FStar_String.lowercase uu____2418  in
    mk_string uu____2417
  
let rec (specs_with_types :
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2435  ->
    let uu____2446 =
      let uu____2457 =
        let uu____2468 =
          let uu____2477 = let uu____2478 = mk_bool true  in Const uu____2478
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2477,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
           in
        let uu____2479 =
          let uu____2490 =
            let uu____2501 =
              let uu____2512 =
                let uu____2523 =
                  let uu____2534 =
                    let uu____2545 =
                      let uu____2556 =
                        let uu____2567 =
                          let uu____2576 =
                            let uu____2577 = mk_bool true  in
                            Const uu____2577  in
                          (FStar_Getopt.noshort, "detail_errors", uu____2576,
                            "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                           in
                        let uu____2578 =
                          let uu____2589 =
                            let uu____2598 =
                              let uu____2599 = mk_bool true  in
                              Const uu____2599  in
                            (FStar_Getopt.noshort, "detail_hint_replay",
                              uu____2598,
                              "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                             in
                          let uu____2600 =
                            let uu____2611 =
                              let uu____2620 =
                                let uu____2621 = mk_bool true  in
                                Const uu____2621  in
                              (FStar_Getopt.noshort, "doc", uu____2620,
                                "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                               in
                            let uu____2622 =
                              let uu____2633 =
                                let uu____2644 =
                                  let uu____2653 =
                                    let uu____2654 = mk_bool true  in
                                    Const uu____2654  in
                                  (FStar_Getopt.noshort, "eager_inference",
                                    uu____2653,
                                    "Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                   in
                                let uu____2655 =
                                  let uu____2666 =
                                    let uu____2677 =
                                      let uu____2688 =
                                        let uu____2699 =
                                          let uu____2708 =
                                            let uu____2709 = mk_bool true  in
                                            Const uu____2709  in
                                          (FStar_Getopt.noshort,
                                            "expose_interfaces", uu____2708,
                                            "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                           in
                                        let uu____2710 =
                                          let uu____2721 =
                                            let uu____2732 =
                                              let uu____2741 =
                                                let uu____2742 = mk_bool true
                                                   in
                                                Const uu____2742  in
                                              (FStar_Getopt.noshort,
                                                "hide_uvar_nums", uu____2741,
                                                "Don't print unification variable numbers")
                                               in
                                            let uu____2743 =
                                              let uu____2754 =
                                                let uu____2765 =
                                                  let uu____2774 =
                                                    let uu____2775 =
                                                      mk_bool true  in
                                                    Const uu____2775  in
                                                  (FStar_Getopt.noshort,
                                                    "hint_info", uu____2774,
                                                    "Print information regarding hints (deprecated; use --query_stats instead)")
                                                   in
                                                let uu____2776 =
                                                  let uu____2787 =
                                                    let uu____2796 =
                                                      let uu____2797 =
                                                        mk_bool true  in
                                                      Const uu____2797  in
                                                    (FStar_Getopt.noshort,
                                                      "in", uu____2796,
                                                      "Legacy interactive mode; reads input from stdin")
                                                     in
                                                  let uu____2798 =
                                                    let uu____2809 =
                                                      let uu____2818 =
                                                        let uu____2819 =
                                                          mk_bool true  in
                                                        Const uu____2819  in
                                                      (FStar_Getopt.noshort,
                                                        "ide", uu____2818,
                                                        "JSON-based interactive mode for IDEs")
                                                       in
                                                    let uu____2820 =
                                                      let uu____2831 =
                                                        let uu____2842 =
                                                          let uu____2851 =
                                                            let uu____2852 =
                                                              mk_bool true
                                                               in
                                                            Const uu____2852
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "indent",
                                                            uu____2851,
                                                            "Parses and outputs the files on the command line")
                                                           in
                                                        let uu____2853 =
                                                          let uu____2864 =
                                                            let uu____2875 =
                                                              let uu____2886
                                                                =
                                                                let uu____2895
                                                                  =
                                                                  let uu____2896
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                  Const
                                                                    uu____2896
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "lax",
                                                                  uu____2895,
                                                                  "Run the lax-type checker only (admit all verification conditions)")
                                                                 in
                                                              let uu____2897
                                                                =
                                                                let uu____2908
                                                                  =
                                                                  let uu____2919
                                                                    =
                                                                    let uu____2928
                                                                    =
                                                                    let uu____2929
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____2929
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____2928,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                  let uu____2930
                                                                    =
                                                                    let uu____2941
                                                                    =
                                                                    let uu____2950
                                                                    =
                                                                    let uu____2951
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____2951
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____2950,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____2952
                                                                    =
                                                                    let uu____2963
                                                                    =
                                                                    let uu____2974
                                                                    =
                                                                    let uu____2985
                                                                    =
                                                                    let uu____2996
                                                                    =
                                                                    let uu____3005
                                                                    =
                                                                    let uu____3006
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3006
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3005,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3007
                                                                    =
                                                                    let uu____3018
                                                                    =
                                                                    let uu____3029
                                                                    =
                                                                    let uu____3038
                                                                    =
                                                                    let uu____3039
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3039
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3038,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3040
                                                                    =
                                                                    let uu____3051
                                                                    =
                                                                    let uu____3062
                                                                    =
                                                                    let uu____3071
                                                                    =
                                                                    let uu____3072
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3072
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3071,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3073
                                                                    =
                                                                    let uu____3084
                                                                    =
                                                                    let uu____3093
                                                                    =
                                                                    let uu____3094
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3094
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3093,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3095
                                                                    =
                                                                    let uu____3106
                                                                    =
                                                                    let uu____3115
                                                                    =
                                                                    let uu____3116
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3116
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3115,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3117
                                                                    =
                                                                    let uu____3128
                                                                    =
                                                                    let uu____3139
                                                                    =
                                                                    let uu____3150
                                                                    =
                                                                    let uu____3159
                                                                    =
                                                                    let uu____3160
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3160
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3159,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3161
                                                                    =
                                                                    let uu____3172
                                                                    =
                                                                    let uu____3181
                                                                    =
                                                                    let uu____3182
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3182
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3181,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3183
                                                                    =
                                                                    let uu____3194
                                                                    =
                                                                    let uu____3203
                                                                    =
                                                                    let uu____3204
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3204
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3203,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3205
                                                                    =
                                                                    let uu____3216
                                                                    =
                                                                    let uu____3225
                                                                    =
                                                                    let uu____3226
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3226
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3225,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3227
                                                                    =
                                                                    let uu____3238
                                                                    =
                                                                    let uu____3247
                                                                    =
                                                                    let uu____3248
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3248
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3247,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3249
                                                                    =
                                                                    let uu____3260
                                                                    =
                                                                    let uu____3269
                                                                    =
                                                                    let uu____3270
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3270
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3269,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3271
                                                                    =
                                                                    let uu____3282
                                                                    =
                                                                    let uu____3291
                                                                    =
                                                                    let uu____3292
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3292
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3291,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3293
                                                                    =
                                                                    let uu____3304
                                                                    =
                                                                    let uu____3313
                                                                    =
                                                                    let uu____3314
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3314
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3313,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3315
                                                                    =
                                                                    let uu____3326
                                                                    =
                                                                    let uu____3335
                                                                    =
                                                                    let uu____3336
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3336
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3335,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3337
                                                                    =
                                                                    let uu____3348
                                                                    =
                                                                    let uu____3359
                                                                    =
                                                                    let uu____3368
                                                                    =
                                                                    let uu____3369
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3369
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3368,
                                                                    " ")  in
                                                                    let uu____3370
                                                                    =
                                                                    let uu____3381
                                                                    =
                                                                    let uu____3392
                                                                    =
                                                                    let uu____3403
                                                                    =
                                                                    let uu____3414
                                                                    =
                                                                    let uu____3425
                                                                    =
                                                                    let uu____3434
                                                                    =
                                                                    let uu____3435
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3435
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____3434,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____3436
                                                                    =
                                                                    let uu____3447
                                                                    =
                                                                    let uu____3456
                                                                    =
                                                                    let uu____3457
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3457
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3456,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____3458
                                                                    =
                                                                    let uu____3469
                                                                    =
                                                                    let uu____3480
                                                                    =
                                                                    let uu____3489
                                                                    =
                                                                    let uu____3490
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3490
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3489,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____3491
                                                                    =
                                                                    let uu____3502
                                                                    =
                                                                    let uu____3511
                                                                    =
                                                                    let uu____3512
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3512
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3511,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____3513
                                                                    =
                                                                    let uu____3524
                                                                    =
                                                                    let uu____3533
                                                                    =
                                                                    let uu____3534
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3534
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3533,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____3535
                                                                    =
                                                                    let uu____3546
                                                                    =
                                                                    let uu____3555
                                                                    =
                                                                    let uu____3556
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3556
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____3555,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____3557
                                                                    =
                                                                    let uu____3568
                                                                    =
                                                                    let uu____3577
                                                                    =
                                                                    let uu____3578
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3578
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____3577,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____3579
                                                                    =
                                                                    let uu____3590
                                                                    =
                                                                    let uu____3599
                                                                    =
                                                                    let uu____3600
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3600
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____3599,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____3601
                                                                    =
                                                                    let uu____3612
                                                                    =
                                                                    let uu____3621
                                                                    =
                                                                    let uu____3622
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3622
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____3621,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____3623
                                                                    =
                                                                    let uu____3634
                                                                    =
                                                                    let uu____3643
                                                                    =
                                                                    let uu____3644
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3644
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____3643,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____3645
                                                                    =
                                                                    let uu____3656
                                                                    =
                                                                    let uu____3667
                                                                    =
                                                                    let uu____3676
                                                                    =
                                                                    let uu____3677
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3677
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____3676,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____3678
                                                                    =
                                                                    let uu____3689
                                                                    =
                                                                    let uu____3700
                                                                    =
                                                                    let uu____3711
                                                                    =
                                                                    let uu____3722
                                                                    =
                                                                    let uu____3731
                                                                    =
                                                                    let uu____3732
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3732
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____3731,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____3733
                                                                    =
                                                                    let uu____3744
                                                                    =
                                                                    let uu____3754
                                                                    =
                                                                    let uu____3755
                                                                    =
                                                                    let uu____3762
                                                                    =
                                                                    let uu____3763
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3763
                                                                     in
                                                                    ((fun
                                                                    uu____3768
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____3762)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____3755
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____3754,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____3772
                                                                    =
                                                                    let uu____3784
                                                                    =
                                                                    let uu____3793
                                                                    =
                                                                    let uu____3794
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3794
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____3793,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____3795
                                                                    =
                                                                    let uu____3806
                                                                    =
                                                                    let uu____3817
                                                                    =
                                                                    let uu____3826
                                                                    =
                                                                    let uu____3827
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3827
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____3826,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____3828
                                                                    =
                                                                    let uu____3839
                                                                    =
                                                                    let uu____3850
                                                                    =
                                                                    let uu____3861
                                                                    =
                                                                    let uu____3872
                                                                    =
                                                                    let uu____3883
                                                                    =
                                                                    let uu____3892
                                                                    =
                                                                    let uu____3893
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3893
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____3892,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____3894
                                                                    =
                                                                    let uu____3905
                                                                    =
                                                                    let uu____3914
                                                                    =
                                                                    let uu____3915
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3915
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____3914,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____3916
                                                                    =
                                                                    let uu____3927
                                                                    =
                                                                    let uu____3938
                                                                    =
                                                                    let uu____3947
                                                                    =
                                                                    let uu____3948
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3948
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    uu____3947,
                                                                    "Extract interfaces from the dependencies and use them for verification")
                                                                     in
                                                                    let uu____3949
                                                                    =
                                                                    let uu____3960
                                                                    =
                                                                    let uu____3970
                                                                    =
                                                                    let uu____3971
                                                                    =
                                                                    let uu____3978
                                                                    =
                                                                    let uu____3979
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3979
                                                                     in
                                                                    ((fun
                                                                    uu____3984
                                                                     ->
                                                                    (
                                                                    let uu____3986
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____3986);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____3978)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____3971
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____3970,
                                                                    "Display this information")
                                                                     in
                                                                    let uu____4001
                                                                    =
                                                                    let uu____4013
                                                                    =
                                                                    let uu____4022
                                                                    =
                                                                    let uu____4023
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4023
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_reduction_under_match",
                                                                    uu____4022,
                                                                    "Temporary flag ... not described")
                                                                     in
                                                                    [uu____4013]
                                                                     in
                                                                    uu____3960
                                                                    ::
                                                                    uu____4001
                                                                     in
                                                                    uu____3938
                                                                    ::
                                                                    uu____3949
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____3927
                                                                     in
                                                                    uu____3905
                                                                    ::
                                                                    uu____3916
                                                                     in
                                                                    uu____3883
                                                                    ::
                                                                    uu____3894
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'false')")
                                                                    ::
                                                                    uu____3872
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____3861
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____3850
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____3839
                                                                     in
                                                                    uu____3817
                                                                    ::
                                                                    uu____3828
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____3806
                                                                     in
                                                                    uu____3784
                                                                    ::
                                                                    uu____3795
                                                                     in
                                                                    uu____3744
                                                                    ::
                                                                    uu____3772
                                                                     in
                                                                    uu____3722
                                                                    ::
                                                                    uu____3733
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____3711
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____3700
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____3689
                                                                     in
                                                                    uu____3667
                                                                    ::
                                                                    uu____3678
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____3656
                                                                     in
                                                                    uu____3634
                                                                    ::
                                                                    uu____3645
                                                                     in
                                                                    uu____3612
                                                                    ::
                                                                    uu____3623
                                                                     in
                                                                    uu____3590
                                                                    ::
                                                                    uu____3601
                                                                     in
                                                                    uu____3568
                                                                    ::
                                                                    uu____3579
                                                                     in
                                                                    uu____3546
                                                                    ::
                                                                    uu____3557
                                                                     in
                                                                    uu____3524
                                                                    ::
                                                                    uu____3535
                                                                     in
                                                                    uu____3502
                                                                    ::
                                                                    uu____3513
                                                                     in
                                                                    uu____3480
                                                                    ::
                                                                    uu____3491
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3469
                                                                     in
                                                                    uu____3447
                                                                    ::
                                                                    uu____3458
                                                                     in
                                                                    uu____3425
                                                                    ::
                                                                    uu____3436
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3414
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3403
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3392
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3381
                                                                     in
                                                                    uu____3359
                                                                    ::
                                                                    uu____3370
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3348
                                                                     in
                                                                    uu____3326
                                                                    ::
                                                                    uu____3337
                                                                     in
                                                                    uu____3304
                                                                    ::
                                                                    uu____3315
                                                                     in
                                                                    uu____3282
                                                                    ::
                                                                    uu____3293
                                                                     in
                                                                    uu____3260
                                                                    ::
                                                                    uu____3271
                                                                     in
                                                                    uu____3238
                                                                    ::
                                                                    uu____3249
                                                                     in
                                                                    uu____3216
                                                                    ::
                                                                    uu____3227
                                                                     in
                                                                    uu____3194
                                                                    ::
                                                                    uu____3205
                                                                     in
                                                                    uu____3172
                                                                    ::
                                                                    uu____3183
                                                                     in
                                                                    uu____3150
                                                                    ::
                                                                    uu____3161
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3139
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3128
                                                                     in
                                                                    uu____3106
                                                                    ::
                                                                    uu____3117
                                                                     in
                                                                    uu____3084
                                                                    ::
                                                                    uu____3095
                                                                     in
                                                                    uu____3062
                                                                    ::
                                                                    uu____3073
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3051
                                                                     in
                                                                    uu____3029
                                                                    ::
                                                                    uu____3040
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3018
                                                                     in
                                                                    uu____2996
                                                                    ::
                                                                    uu____3007
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____2985
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____2974
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____2963
                                                                     in
                                                                    uu____2941
                                                                    ::
                                                                    uu____2952
                                                                     in
                                                                  uu____2919
                                                                    ::
                                                                    uu____2930
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "load",
                                                                  (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                  "Load compiled module")
                                                                  ::
                                                                  uu____2908
                                                                 in
                                                              uu____2886 ::
                                                                uu____2897
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "initial_ifuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                              :: uu____2875
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "initial_fuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of recursive functions to try initially (default 2)")
                                                            :: uu____2864
                                                           in
                                                        uu____2842 ::
                                                          uu____2853
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "include",
                                                        (ReverseAccumulated
                                                           (PathStr "path")),
                                                        "A directory in which to search for files included on the command line")
                                                        :: uu____2831
                                                       in
                                                    uu____2809 :: uu____2820
                                                     in
                                                  uu____2787 :: uu____2798
                                                   in
                                                uu____2765 :: uu____2776  in
                                              (FStar_Getopt.noshort,
                                                "hint_file",
                                                (PathStr "path"),
                                                "Read/write hints to <path> (instead of module-specific hints files)")
                                                :: uu____2754
                                               in
                                            uu____2732 :: uu____2743  in
                                          (FStar_Getopt.noshort,
                                            "fstar_home", (PathStr "dir"),
                                            "Set the FSTAR_HOME variable to <dir>")
                                            :: uu____2721
                                           in
                                        uu____2699 :: uu____2710  in
                                      (FStar_Getopt.noshort,
                                        "extract_namespace",
                                        (Accumulated
                                           (PostProcessed
                                              (pp_lowercase,
                                                (SimpleStr "namespace name")))),
                                        "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                        :: uu____2688
                                       in
                                    (FStar_Getopt.noshort, "extract_module",
                                      (Accumulated
                                         (PostProcessed
                                            (pp_lowercase,
                                              (SimpleStr "module_name")))),
                                      "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                      :: uu____2677
                                     in
                                  (FStar_Getopt.noshort, "extract",
                                    (Accumulated
                                       (SimpleStr
                                          "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                    "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                    :: uu____2666
                                   in
                                uu____2644 :: uu____2655  in
                              (FStar_Getopt.noshort, "dump_module",
                                (Accumulated (SimpleStr "module_name")), "")
                                :: uu____2633
                               in
                            uu____2611 :: uu____2622  in
                          uu____2589 :: uu____2600  in
                        uu____2567 :: uu____2578  in
                      (FStar_Getopt.noshort, "dep",
                        (EnumStr ["make"; "graph"; "full"]),
                        "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                        :: uu____2556
                       in
                    (FStar_Getopt.noshort, "defensive",
                      (EnumStr ["no"; "warn"; "fail"]),
                      "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                      :: uu____2545
                     in
                  (FStar_Getopt.noshort, "debug_level",
                    (Accumulated
                       (OpenEnumStr
                          (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                    "Control the verbosity of debugging info") :: uu____2534
                   in
                (FStar_Getopt.noshort, "debug",
                  (Accumulated (SimpleStr "module_name")),
                  "Print lots of debugging information while checking module")
                  :: uu____2523
                 in
              (FStar_Getopt.noshort, "codegen-lib",
                (Accumulated (SimpleStr "namespace")),
                "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                :: uu____2512
               in
            (FStar_Getopt.noshort, "codegen",
              (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
              "Generate code for further compilation to executable code, or build a compiler plugin")
              :: uu____2501
             in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2490
           in
        uu____2468 :: uu____2479  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2457
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2446

and (specs : Prims.unit -> FStar_Getopt.opt Prims.list) =
  fun uu____4772  ->
    let uu____4775 = specs_with_types ()  in
    FStar_List.map
      (fun uu____4800  ->
         match uu____4800 with
         | (short,long,typ,doc) ->
             let uu____4813 =
               let uu____4824 = arg_spec_of_opt_type long typ  in
               (short, long, uu____4824, doc)  in
             mk_spec uu____4813) uu____4775

let (settable : Prims.string -> Prims.bool) =
  fun uu___44_4831  ->
    match uu___44_4831 with
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
    | uu____4832 -> false
  
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
       (fun uu____4889  ->
          match uu____4889 with
          | (uu____4900,x,uu____4902,uu____4903) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____4949  ->
          match uu____4949 with
          | (uu____4960,x,uu____4962,uu____4963) -> resettable x))
  
let (display_usage : Prims.unit -> Prims.unit) =
  fun uu____4970  ->
    let uu____4971 = specs ()  in display_usage_aux uu____4971
  
let (fstar_home : Prims.unit -> Prims.string) =
  fun uu____4986  ->
    let uu____4987 = get_fstar_home ()  in
    match uu____4987 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir ()  in
        let x1 = Prims.strcat x "/.."  in
        ((let uu____4993 =
            let uu____4998 = mk_string x1  in ("fstar_home", uu____4998)  in
          set_option' uu____4993);
         x1)
    | FStar_Pervasives_Native.Some x -> x
  
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5006 -> true
    | uu____5007 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5014 -> uu____5014
  
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
          let uu____5058 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5058
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5084  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5089 =
             let uu____5092 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5092 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5089)
       in
    let uu____5141 =
      let uu____5144 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5144
       in
    (res, uu____5141)
  
let (file_list : Prims.unit -> Prims.string Prims.list) =
  fun uu____5176  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____5209 = specs ()  in
       FStar_Getopt.parse_cmdline uu____5209 (fun x  -> ())  in
     (let uu____5215 =
        let uu____5220 =
          let uu____5221 = FStar_List.map mk_string old_verify_module  in
          List uu____5221  in
        ("verify_module", uu____5220)  in
      set_option' uu____5215);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____5229 =
        let uu____5230 =
          let uu____5231 =
            let uu____5232 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____5232  in
          (FStar_String.length f1) - uu____5231  in
        uu____5230 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5229  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5236 = get_lax ()  in
    if uu____5236
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____5244 = module_name_of_file_name fn  in should_verify uu____5244
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5248 = get___temp_no_proj ()  in
    FStar_List.contains m uu____5248
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5254 = should_verify m  in
    if uu____5254 then m <> "Prims" else false
  
let (include_path : Prims.unit -> Prims.string Prims.list) =
  fun uu____5260  ->
    let uu____5261 = get_no_default_includes ()  in
    if uu____5261
    then get_include ()
    else
      (let h = fstar_home ()  in
       let defs = universe_include_path_base_dirs  in
       let uu____5269 =
         let uu____5272 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x))
            in
         FStar_All.pipe_right uu____5272
           (FStar_List.filter FStar_Util.file_exists)
          in
       let uu____5285 =
         let uu____5288 = get_include ()  in
         FStar_List.append uu____5288 ["."]  in
       FStar_List.append uu____5269 uu____5285)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun filename  ->
    let uu____5296 = FStar_Util.is_path_absolute filename  in
    if uu____5296
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5303 =
         let uu____5306 = include_path ()  in FStar_List.rev uu____5306  in
       FStar_Util.find_map uu____5303
         (fun p  ->
            let path =
              if p = "." then filename else FStar_Util.join_paths p filename
               in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
  
let (prims : Prims.unit -> Prims.string) =
  fun uu____5319  ->
    let uu____5320 = get_prims ()  in
    match uu____5320 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____5324 = find_file filename  in
        (match uu____5324 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5328 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____5328)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : Prims.unit -> Prims.string) =
  fun uu____5332  ->
    let uu____5333 = prims ()  in FStar_Util.basename uu____5333
  
let (pervasives : Prims.unit -> Prims.string) =
  fun uu____5336  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____5338 = find_file filename  in
    match uu____5338 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5342 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5342
  
let (pervasives_basename : Prims.unit -> Prims.string) =
  fun uu____5345  ->
    let uu____5346 = pervasives ()  in FStar_Util.basename uu____5346
  
let (pervasives_native_basename : Prims.unit -> Prims.string) =
  fun uu____5349  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____5351 = find_file filename  in
    match uu____5351 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5355 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5355
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____5359 = get_odir ()  in
    match uu____5359 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____5366 = get_cache_dir ()  in
    match uu____5366 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____5370 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____5370
  
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
             let uu____5420 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             FStar_Ident.path_of_text uu____5420  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           let uu____5424 = FStar_Ident.path_of_text s1  in
           (uu____5424, true))
       in
    let uu____5425 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____5425 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____5493 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____5493 (FStar_List.contains s)
  
let (__temp_fast_implicits : Prims.unit -> Prims.bool) =
  fun uu____5500  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : Prims.unit -> Prims.bool) =
  fun uu____5503  -> get_admit_smt_queries () 
let (admit_except :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5508  -> get_admit_except () 
let (cache_checked_modules : Prims.unit -> Prims.bool) =
  fun uu____5511  -> get_cache_checked_modules () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin [@@deriving show]
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____5515 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____5519 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____5523 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____5527 -> false
  
let (codegen : Prims.unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____5532  ->
    let uu____5533 = get_codegen ()  in
    FStar_Util.map_opt uu____5533
      (fun uu___45_5537  ->
         match uu___45_5537 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____5538 -> failwith "Impossible")
  
let (codegen_libs : Prims.unit -> Prims.string Prims.list Prims.list) =
  fun uu____5545  ->
    let uu____5546 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____5546
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : Prims.unit -> Prims.bool) =
  fun uu____5561  -> let uu____5562 = get_debug ()  in uu____5562 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____5570 = get_debug ()  in
    FStar_All.pipe_right uu____5570 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____5583 = get_debug ()  in
       FStar_All.pipe_right uu____5583 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : Prims.unit -> Prims.bool) =
  fun uu____5590  -> let uu____5591 = get_defensive ()  in uu____5591 <> "no" 
let (defensive_fail : Prims.unit -> Prims.bool) =
  fun uu____5594  ->
    let uu____5595 = get_defensive ()  in uu____5595 = "fail"
  
let (dep : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5600  -> get_dep () 
let (detail_errors : Prims.unit -> Prims.bool) =
  fun uu____5603  -> get_detail_errors () 
let (detail_hint_replay : Prims.unit -> Prims.bool) =
  fun uu____5606  -> get_detail_hint_replay () 
let (doc : Prims.unit -> Prims.bool) = fun uu____5609  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____5613 = get_dump_module ()  in
    FStar_All.pipe_right uu____5613 (FStar_List.contains s)
  
let (eager_inference : Prims.unit -> Prims.bool) =
  fun uu____5620  -> get_eager_inference () 
let (expose_interfaces : Prims.unit -> Prims.bool) =
  fun uu____5623  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____5627 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____5627
  
let (full_context_dependency : Prims.unit -> Prims.bool) =
  fun uu____5655  -> true 
let (hide_uvar_nums : Prims.unit -> Prims.bool) =
  fun uu____5658  -> get_hide_uvar_nums () 
let (hint_info : Prims.unit -> Prims.bool) =
  fun uu____5661  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5666  -> get_hint_file () 
let (ide : Prims.unit -> Prims.bool) = fun uu____5669  -> get_ide () 
let (indent : Prims.unit -> Prims.bool) = fun uu____5672  -> get_indent () 
let (initial_fuel : Prims.unit -> Prims.int) =
  fun uu____5675  ->
    let uu____5676 = get_initial_fuel ()  in
    let uu____5677 = get_max_fuel ()  in Prims.min uu____5676 uu____5677
  
let (initial_ifuel : Prims.unit -> Prims.int) =
  fun uu____5680  ->
    let uu____5681 = get_initial_ifuel ()  in
    let uu____5682 = get_max_ifuel ()  in Prims.min uu____5681 uu____5682
  
let (interactive : Prims.unit -> Prims.bool) =
  fun uu____5685  -> (get_in ()) || (get_ide ()) 
let (lax : Prims.unit -> Prims.bool) = fun uu____5688  -> get_lax () 
let (load : Prims.unit -> Prims.string Prims.list) =
  fun uu____5693  -> get_load () 
let (legacy_interactive : Prims.unit -> Prims.bool) =
  fun uu____5696  -> get_in () 
let (log_queries : Prims.unit -> Prims.bool) =
  fun uu____5699  -> get_log_queries () 
let (log_types : Prims.unit -> Prims.bool) =
  fun uu____5702  -> get_log_types () 
let (max_fuel : Prims.unit -> Prims.int) = fun uu____5705  -> get_max_fuel () 
let (max_ifuel : Prims.unit -> Prims.int) =
  fun uu____5708  -> get_max_ifuel () 
let (min_fuel : Prims.unit -> Prims.int) = fun uu____5711  -> get_min_fuel () 
let (ml_ish : Prims.unit -> Prims.bool) = fun uu____5714  -> get_MLish () 
let (set_ml_ish : Prims.unit -> Prims.unit) =
  fun uu____5717  -> set_option "MLish" (Bool true) 
let (n_cores : Prims.unit -> Prims.int) = fun uu____5720  -> get_n_cores () 
let (no_default_includes : Prims.unit -> Prims.bool) =
  fun uu____5723  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____5728 = get_no_extract ()  in
    FStar_All.pipe_right uu____5728
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : Prims.unit -> Prims.bool) =
  fun uu____5737  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : Prims.unit -> Prims.bool) =
  fun uu____5740  -> get_no_location_info () 
let (no_smt : Prims.unit -> Prims.bool) = fun uu____5743  -> get_no_smt () 
let (output_dir : Prims.unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____5748  -> get_odir () 
let (ugly : Prims.unit -> Prims.bool) = fun uu____5751  -> get_ugly () 
let (print_bound_var_types : Prims.unit -> Prims.bool) =
  fun uu____5754  -> get_print_bound_var_types () 
let (print_effect_args : Prims.unit -> Prims.bool) =
  fun uu____5757  -> get_print_effect_args () 
let (print_implicits : Prims.unit -> Prims.bool) =
  fun uu____5760  -> get_print_implicits () 
let (print_real_names : Prims.unit -> Prims.bool) =
  fun uu____5763  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : Prims.unit -> Prims.bool) =
  fun uu____5766  -> get_print_universes () 
let (print_z3_statistics : Prims.unit -> Prims.bool) =
  fun uu____5769  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : Prims.unit -> Prims.bool) =
  fun uu____5772  -> get_query_stats () 
let (record_hints : Prims.unit -> Prims.bool) =
  fun uu____5775  -> get_record_hints () 
let (reuse_hint_for :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5780  -> get_reuse_hint_for () 
let (silent : Prims.unit -> Prims.bool) = fun uu____5783  -> get_silent () 
let (smtencoding_elim_box : Prims.unit -> Prims.bool) =
  fun uu____5786  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : Prims.unit -> Prims.bool) =
  fun uu____5789  ->
    let uu____5790 = get_smtencoding_nl_arith_repr ()  in
    uu____5790 = "native"
  
let (smtencoding_nl_arith_wrapped : Prims.unit -> Prims.bool) =
  fun uu____5793  ->
    let uu____5794 = get_smtencoding_nl_arith_repr ()  in
    uu____5794 = "wrapped"
  
let (smtencoding_nl_arith_default : Prims.unit -> Prims.bool) =
  fun uu____5797  ->
    let uu____5798 = get_smtencoding_nl_arith_repr ()  in
    uu____5798 = "boxwrap"
  
let (smtencoding_l_arith_native : Prims.unit -> Prims.bool) =
  fun uu____5801  ->
    let uu____5802 = get_smtencoding_l_arith_repr ()  in
    uu____5802 = "native"
  
let (smtencoding_l_arith_default : Prims.unit -> Prims.bool) =
  fun uu____5805  ->
    let uu____5806 = get_smtencoding_l_arith_repr ()  in
    uu____5806 = "boxwrap"
  
let (tactic_raw_binders : Prims.unit -> Prims.bool) =
  fun uu____5809  -> get_tactic_raw_binders () 
let (tactic_trace : Prims.unit -> Prims.bool) =
  fun uu____5812  -> get_tactic_trace () 
let (tactic_trace_d : Prims.unit -> Prims.int) =
  fun uu____5815  -> get_tactic_trace_d () 
let (timing : Prims.unit -> Prims.bool) = fun uu____5818  -> get_timing () 
let (trace_error : Prims.unit -> Prims.bool) =
  fun uu____5821  -> get_trace_error () 
let (unthrottle_inductives : Prims.unit -> Prims.bool) =
  fun uu____5824  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : Prims.unit -> Prims.bool) =
  fun uu____5827  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : Prims.unit -> Prims.bool) =
  fun uu____5830  -> get_use_eq_at_higher_order () 
let (use_hints : Prims.unit -> Prims.bool) =
  fun uu____5833  -> get_use_hints () 
let (use_hint_hashes : Prims.unit -> Prims.bool) =
  fun uu____5836  -> get_use_hint_hashes () 
let (use_native_tactics :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5841  -> get_use_native_tactics () 
let (use_tactics : Prims.unit -> Prims.bool) =
  fun uu____5844  -> get_use_tactics () 
let (using_facts_from :
  Prims.unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____5853  ->
    let uu____5854 = get_using_facts_from ()  in
    match uu____5854 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : Prims.unit -> Prims.bool) =
  fun uu____5888  ->
    let uu____5889 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____5889
  
let (vcgen_decorate_with_type : Prims.unit -> Prims.bool) =
  fun uu____5894  ->
    let uu____5895 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____5895 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____5898 -> false
  
let (warn_default_effects : Prims.unit -> Prims.bool) =
  fun uu____5903  -> get_warn_default_effects () 
let (z3_exe : Prims.unit -> Prims.string) =
  fun uu____5906  ->
    let uu____5907 = get_smt ()  in
    match uu____5907 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : Prims.unit -> Prims.string Prims.list) =
  fun uu____5915  -> get_z3cliopt () 
let (z3_refresh : Prims.unit -> Prims.bool) =
  fun uu____5918  -> get_z3refresh () 
let (z3_rlimit : Prims.unit -> Prims.int) =
  fun uu____5921  -> get_z3rlimit () 
let (z3_rlimit_factor : Prims.unit -> Prims.int) =
  fun uu____5924  -> get_z3rlimit_factor () 
let (z3_seed : Prims.unit -> Prims.int) = fun uu____5927  -> get_z3seed () 
let (use_two_phase_tc : Prims.unit -> Prims.bool) =
  fun uu____5930  -> get_use_two_phase_tc () 
let (no_positivity : Prims.unit -> Prims.bool) =
  fun uu____5933  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : Prims.unit -> Prims.bool) =
  fun uu____5936  -> get_ml_no_eta_expand_coertions () 
let (warn_error : Prims.unit -> Prims.string) =
  fun uu____5939  -> get_warn_error () 
let (use_extracted_interfaces : Prims.unit -> Prims.bool) =
  fun uu____5942  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____5947 = get_extract ()  in
    match uu____5947 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____5958 =
            let uu____5971 = get_no_extract ()  in
            let uu____5974 = get_extract_namespace ()  in
            let uu____5977 = get_extract_module ()  in
            (uu____5971, uu____5974, uu____5977)  in
          match uu____5958 with
          | ([],[],[]) -> ()
          | uu____5992 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = FStar_Ident.path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____6034,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____6053 -> false  in
          let uu____6062 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____6096  ->
                    match uu____6096 with
                    | (path,uu____6104) -> matches_path m_components path))
             in
          match uu____6062 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____6115,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____6133 = get_extract_namespace ()  in
          match uu____6133 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____6147 = get_extract_module ()  in
          match uu____6147 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____6159 = no_extract m1  in Prims.op_Negation uu____6159) &&
          (let uu____6161 =
             let uu____6170 = get_extract_namespace ()  in
             let uu____6173 = get_extract_module ()  in
             (uu____6170, uu____6173)  in
           (match uu____6161 with
            | ([],[]) -> true
            | uu____6184 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  