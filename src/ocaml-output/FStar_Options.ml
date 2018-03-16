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
  fun uu___36_232  ->
    match uu___36_232 with
    | Bool b -> b
    | uu____234 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___37_237  ->
    match uu___37_237 with
    | Int b -> b
    | uu____239 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___38_242  ->
    match uu___38_242 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____245 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___39_250  ->
    match uu___39_250 with
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
    fun uu___40_301  ->
      match uu___40_301 with
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
  fun uu____1025  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : Prims.unit -> Prims.unit) =
  fun uu____1040  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : Prims.unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1099 =
      let uu____1102 = peek ()  in FStar_Util.smap_try_find uu____1102 s  in
    match uu____1099 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1109 . Prims.string -> (option_val -> 'Auu____1109) -> 'Auu____1109
  = fun s  -> fun c  -> c (get_option s) 
let (get_admit_smt_queries : Prims.unit -> Prims.bool) =
  fun uu____1125  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1130  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : Prims.unit -> Prims.bool) =
  fun uu____1135  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1140  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_codegen : Prims.unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1147  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : Prims.unit -> Prims.string Prims.list) =
  fun uu____1154  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : Prims.unit -> Prims.string Prims.list) =
  fun uu____1161  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : Prims.unit -> Prims.string Prims.list) =
  fun uu____1168  -> lookup_opt "debug_level" (as_list as_string) 
let (get_defensive : Prims.unit -> Prims.string) =
  fun uu____1173  -> lookup_opt "defensive" as_string 
let (get_dep : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1178  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : Prims.unit -> Prims.bool) =
  fun uu____1183  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : Prims.unit -> Prims.bool) =
  fun uu____1186  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : Prims.unit -> Prims.bool) =
  fun uu____1189  -> lookup_opt "doc" as_bool 
let (get_dump_module : Prims.unit -> Prims.string Prims.list) =
  fun uu____1194  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_inference : Prims.unit -> Prims.bool) =
  fun uu____1199  -> lookup_opt "eager_inference" as_bool 
let (get_expose_interfaces : Prims.unit -> Prims.bool) =
  fun uu____1202  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1209  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : Prims.unit -> Prims.string Prims.list) =
  fun uu____1220  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : Prims.unit -> Prims.string Prims.list) =
  fun uu____1227  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : Prims.unit -> Prims.bool) =
  fun uu____1232  -> lookup_opt "fs_typ_app" as_bool 
let (get_fstar_home :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1237  -> lookup_opt "fstar_home" (as_option as_string) 
let (get_hide_uvar_nums : Prims.unit -> Prims.bool) =
  fun uu____1242  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : Prims.unit -> Prims.bool) =
  fun uu____1245  -> lookup_opt "hint_info" as_bool 
let (get_hint_file :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1250  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : Prims.unit -> Prims.bool) =
  fun uu____1255  -> lookup_opt "in" as_bool 
let (get_ide : Prims.unit -> Prims.bool) =
  fun uu____1258  -> lookup_opt "ide" as_bool 
let (get_include : Prims.unit -> Prims.string Prims.list) =
  fun uu____1263  -> lookup_opt "include" (as_list as_string) 
let (get_indent : Prims.unit -> Prims.bool) =
  fun uu____1268  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : Prims.unit -> Prims.int) =
  fun uu____1271  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : Prims.unit -> Prims.int) =
  fun uu____1274  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : Prims.unit -> Prims.bool) =
  fun uu____1277  -> lookup_opt "lax" as_bool 
let (get_load : Prims.unit -> Prims.string Prims.list) =
  fun uu____1282  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : Prims.unit -> Prims.bool) =
  fun uu____1287  -> lookup_opt "log_queries" as_bool 
let (get_log_types : Prims.unit -> Prims.bool) =
  fun uu____1290  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : Prims.unit -> Prims.int) =
  fun uu____1293  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : Prims.unit -> Prims.int) =
  fun uu____1296  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : Prims.unit -> Prims.int) =
  fun uu____1299  -> lookup_opt "min_fuel" as_int 
let (get_MLish : Prims.unit -> Prims.bool) =
  fun uu____1302  -> lookup_opt "MLish" as_bool 
let (get_n_cores : Prims.unit -> Prims.int) =
  fun uu____1305  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : Prims.unit -> Prims.bool) =
  fun uu____1308  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : Prims.unit -> Prims.string Prims.list) =
  fun uu____1313  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : Prims.unit -> Prims.bool) =
  fun uu____1318  -> lookup_opt "no_location_info" as_bool 
let (get_normalize_pure_terms_for_extraction : Prims.unit -> Prims.bool) =
  fun uu____1321  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1326  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : Prims.unit -> Prims.bool) =
  fun uu____1331  -> lookup_opt "ugly" as_bool 
let (get_prims : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1336  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : Prims.unit -> Prims.bool) =
  fun uu____1341  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : Prims.unit -> Prims.bool) =
  fun uu____1344  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : Prims.unit -> Prims.bool) =
  fun uu____1347  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : Prims.unit -> Prims.bool) =
  fun uu____1350  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : Prims.unit -> Prims.bool) =
  fun uu____1353  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : Prims.unit -> Prims.bool) =
  fun uu____1356  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : Prims.unit -> Prims.bool) =
  fun uu____1359  -> lookup_opt "prn" as_bool 
let (get_query_stats : Prims.unit -> Prims.bool) =
  fun uu____1362  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : Prims.unit -> Prims.bool) =
  fun uu____1365  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1370  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : Prims.unit -> Prims.bool) =
  fun uu____1375  -> lookup_opt "silent" as_bool 
let (get_smt : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1380  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : Prims.unit -> Prims.bool) =
  fun uu____1385  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : Prims.unit -> Prims.string) =
  fun uu____1388  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : Prims.unit -> Prims.string) =
  fun uu____1391  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : Prims.unit -> Prims.bool) =
  fun uu____1394  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : Prims.unit -> Prims.bool) =
  fun uu____1397  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : Prims.unit -> Prims.int) =
  fun uu____1400  -> lookup_opt "tactic_trace_d" as_int 
let (get_timing : Prims.unit -> Prims.bool) =
  fun uu____1403  -> lookup_opt "timing" as_bool 
let (get_trace_error : Prims.unit -> Prims.bool) =
  fun uu____1406  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : Prims.unit -> Prims.bool) =
  fun uu____1409  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : Prims.unit -> Prims.bool) =
  fun uu____1412  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : Prims.unit -> Prims.bool) =
  fun uu____1415  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : Prims.unit -> Prims.bool) =
  fun uu____1418  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : Prims.unit -> Prims.bool) =
  fun uu____1421  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1426  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : Prims.unit -> Prims.bool) =
  fun uu____1431  ->
    let uu____1432 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1432
  
let (get_using_facts_from :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1439  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1450  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : Prims.unit -> Prims.string Prims.list) =
  fun uu____1457  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : Prims.unit -> Prims.string Prims.list) =
  fun uu____1464  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : Prims.unit -> Prims.bool) =
  fun uu____1469  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : Prims.unit -> Prims.bool) =
  fun uu____1472  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : Prims.unit -> Prims.string Prims.list) =
  fun uu____1477  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : Prims.unit -> Prims.bool) =
  fun uu____1482  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : Prims.unit -> Prims.int) =
  fun uu____1485  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : Prims.unit -> Prims.int) =
  fun uu____1488  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : Prims.unit -> Prims.int) =
  fun uu____1491  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : Prims.unit -> Prims.bool) =
  fun uu____1494  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : Prims.unit -> Prims.bool) =
  fun uu____1497  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : Prims.unit -> Prims.bool) =
  fun uu____1500  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : Prims.unit -> Prims.string) =
  fun uu____1503  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : Prims.unit -> Prims.bool) =
  fun uu____1506  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___41_1509  ->
    match uu___41_1509 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1517 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1521 = get_debug_level ()  in
    FStar_All.pipe_right uu____1521
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : Prims.unit -> Prims.unit) =
  fun uu____1652  ->
    let uu____1653 =
      let uu____1654 = FStar_ST.op_Bang _version  in
      let uu____1674 = FStar_ST.op_Bang _platform  in
      let uu____1694 = FStar_ST.op_Bang _compiler  in
      let uu____1714 = FStar_ST.op_Bang _date  in
      let uu____1734 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1654
        uu____1674 uu____1694 uu____1714 uu____1734
       in
    FStar_Util.print_string uu____1653
  
let display_usage_aux :
  'Auu____1757 'Auu____1758 .
    ('Auu____1757,Prims.string,'Auu____1758 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> Prims.unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____1805  ->
         match uu____1805 with
         | (uu____1816,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____1827 =
                      let uu____1828 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____1828  in
                    FStar_Util.print_string uu____1827
                  else
                    (let uu____1830 =
                       let uu____1831 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____1831 doc  in
                     FStar_Util.print_string uu____1830)
              | FStar_Getopt.OneArg (uu____1832,argname) ->
                  if doc = ""
                  then
                    let uu____1838 =
                      let uu____1839 = FStar_Util.colorize_bold flag  in
                      let uu____1840 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____1839 uu____1840
                       in
                    FStar_Util.print_string uu____1838
                  else
                    (let uu____1842 =
                       let uu____1843 = FStar_Util.colorize_bold flag  in
                       let uu____1844 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____1843
                         uu____1844 doc
                        in
                     FStar_Util.print_string uu____1842))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____1868 = o  in
    match uu____1868 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____1898 =
                let uu____1899 = f ()  in set_option name uu____1899  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____1910 = f x  in set_option name uu____1910
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____1924 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____1924  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____1943 =
        let uu____1946 = lookup_opt name as_list'  in
        FStar_List.append uu____1946 [value]  in
      mk_list uu____1943
  
let accumulate_string :
  'Auu____1955 .
    Prims.string ->
      ('Auu____1955 -> Prims.string) -> 'Auu____1955 -> Prims.unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____1973 =
          let uu____1974 =
            let uu____1975 = post_processor value  in mk_string uu____1975
             in
          accumulated_option name uu____1974  in
        set_option name uu____1973
  
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
    match projectee with | Const _0 -> true | uu____2053 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2065 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2076 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2081 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2093 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2107 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2131 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2167 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2197 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2209 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2227 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type ->
    (Prims.unit -> Prims.unit,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2259 -> true
    | uu____2260 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2267 -> uu____2267
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2281 ->
              let uu____2282 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2282 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2286 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2286
          | PathStr uu____2289 -> mk_path str_val
          | SimpleStr uu____2290 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2295 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2308 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2308
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
            let uu____2325 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2325
  
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
    | PostProcessed (uu____2358,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2366,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2385 = desc_of_opt_type typ  in
      match uu____2385 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2391  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2403 =
      let uu____2404 = as_string s  in FStar_String.lowercase uu____2404  in
    mk_string uu____2403
  
let rec (specs_with_types :
  Prims.unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2421  ->
    let uu____2432 =
      let uu____2443 =
        let uu____2454 =
          let uu____2463 = let uu____2464 = mk_bool true  in Const uu____2464
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2463,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
           in
        let uu____2465 =
          let uu____2476 =
            let uu____2487 =
              let uu____2498 =
                let uu____2509 =
                  let uu____2520 =
                    let uu____2531 =
                      let uu____2542 =
                        let uu____2553 =
                          let uu____2562 =
                            let uu____2563 = mk_bool true  in
                            Const uu____2563  in
                          (FStar_Getopt.noshort, "detail_errors", uu____2562,
                            "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                           in
                        let uu____2564 =
                          let uu____2575 =
                            let uu____2584 =
                              let uu____2585 = mk_bool true  in
                              Const uu____2585  in
                            (FStar_Getopt.noshort, "detail_hint_replay",
                              uu____2584,
                              "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                             in
                          let uu____2586 =
                            let uu____2597 =
                              let uu____2606 =
                                let uu____2607 = mk_bool true  in
                                Const uu____2607  in
                              (FStar_Getopt.noshort, "doc", uu____2606,
                                "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                               in
                            let uu____2608 =
                              let uu____2619 =
                                let uu____2630 =
                                  let uu____2639 =
                                    let uu____2640 = mk_bool true  in
                                    Const uu____2640  in
                                  (FStar_Getopt.noshort, "eager_inference",
                                    uu____2639,
                                    "Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                   in
                                let uu____2641 =
                                  let uu____2652 =
                                    let uu____2663 =
                                      let uu____2674 =
                                        let uu____2685 =
                                          let uu____2694 =
                                            let uu____2695 = mk_bool true  in
                                            Const uu____2695  in
                                          (FStar_Getopt.noshort,
                                            "expose_interfaces", uu____2694,
                                            "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                           in
                                        let uu____2696 =
                                          let uu____2707 =
                                            let uu____2718 =
                                              let uu____2727 =
                                                let uu____2728 = mk_bool true
                                                   in
                                                Const uu____2728  in
                                              (FStar_Getopt.noshort,
                                                "hide_uvar_nums", uu____2727,
                                                "Don't print unification variable numbers")
                                               in
                                            let uu____2729 =
                                              let uu____2740 =
                                                let uu____2751 =
                                                  let uu____2760 =
                                                    let uu____2761 =
                                                      mk_bool true  in
                                                    Const uu____2761  in
                                                  (FStar_Getopt.noshort,
                                                    "hint_info", uu____2760,
                                                    "Print information regarding hints (deprecated; use --query_stats instead)")
                                                   in
                                                let uu____2762 =
                                                  let uu____2773 =
                                                    let uu____2782 =
                                                      let uu____2783 =
                                                        mk_bool true  in
                                                      Const uu____2783  in
                                                    (FStar_Getopt.noshort,
                                                      "in", uu____2782,
                                                      "Legacy interactive mode; reads input from stdin")
                                                     in
                                                  let uu____2784 =
                                                    let uu____2795 =
                                                      let uu____2804 =
                                                        let uu____2805 =
                                                          mk_bool true  in
                                                        Const uu____2805  in
                                                      (FStar_Getopt.noshort,
                                                        "ide", uu____2804,
                                                        "JSON-based interactive mode for IDEs")
                                                       in
                                                    let uu____2806 =
                                                      let uu____2817 =
                                                        let uu____2828 =
                                                          let uu____2837 =
                                                            let uu____2838 =
                                                              mk_bool true
                                                               in
                                                            Const uu____2838
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "indent",
                                                            uu____2837,
                                                            "Parses and outputs the files on the command line")
                                                           in
                                                        let uu____2839 =
                                                          let uu____2850 =
                                                            let uu____2861 =
                                                              let uu____2872
                                                                =
                                                                let uu____2881
                                                                  =
                                                                  let uu____2882
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                  Const
                                                                    uu____2882
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "lax",
                                                                  uu____2881,
                                                                  "Run the lax-type checker only (admit all verification conditions)")
                                                                 in
                                                              let uu____2883
                                                                =
                                                                let uu____2894
                                                                  =
                                                                  let uu____2905
                                                                    =
                                                                    let uu____2914
                                                                    =
                                                                    let uu____2915
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____2915
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____2914,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                  let uu____2916
                                                                    =
                                                                    let uu____2927
                                                                    =
                                                                    let uu____2936
                                                                    =
                                                                    let uu____2937
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____2937
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____2936,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____2938
                                                                    =
                                                                    let uu____2949
                                                                    =
                                                                    let uu____2960
                                                                    =
                                                                    let uu____2971
                                                                    =
                                                                    let uu____2982
                                                                    =
                                                                    let uu____2991
                                                                    =
                                                                    let uu____2992
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____2992
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____2991,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____2993
                                                                    =
                                                                    let uu____3004
                                                                    =
                                                                    let uu____3015
                                                                    =
                                                                    let uu____3024
                                                                    =
                                                                    let uu____3025
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3025
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3024,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3026
                                                                    =
                                                                    let uu____3037
                                                                    =
                                                                    let uu____3048
                                                                    =
                                                                    let uu____3057
                                                                    =
                                                                    let uu____3058
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3058
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3057,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3059
                                                                    =
                                                                    let uu____3070
                                                                    =
                                                                    let uu____3079
                                                                    =
                                                                    let uu____3080
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3080
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3079,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3081
                                                                    =
                                                                    let uu____3092
                                                                    =
                                                                    let uu____3103
                                                                    =
                                                                    let uu____3114
                                                                    =
                                                                    let uu____3123
                                                                    =
                                                                    let uu____3124
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3124
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3123,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3125
                                                                    =
                                                                    let uu____3136
                                                                    =
                                                                    let uu____3145
                                                                    =
                                                                    let uu____3146
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3146
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3145,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3147
                                                                    =
                                                                    let uu____3158
                                                                    =
                                                                    let uu____3167
                                                                    =
                                                                    let uu____3168
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3168
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3167,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3169
                                                                    =
                                                                    let uu____3180
                                                                    =
                                                                    let uu____3189
                                                                    =
                                                                    let uu____3190
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3190
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3189,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3191
                                                                    =
                                                                    let uu____3202
                                                                    =
                                                                    let uu____3211
                                                                    =
                                                                    let uu____3212
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3212
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3211,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3213
                                                                    =
                                                                    let uu____3224
                                                                    =
                                                                    let uu____3233
                                                                    =
                                                                    let uu____3234
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3234
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3233,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3235
                                                                    =
                                                                    let uu____3246
                                                                    =
                                                                    let uu____3255
                                                                    =
                                                                    let uu____3256
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3256
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3255,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3257
                                                                    =
                                                                    let uu____3268
                                                                    =
                                                                    let uu____3277
                                                                    =
                                                                    let uu____3278
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3278
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3277,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3279
                                                                    =
                                                                    let uu____3290
                                                                    =
                                                                    let uu____3299
                                                                    =
                                                                    let uu____3300
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3300
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3299,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3301
                                                                    =
                                                                    let uu____3312
                                                                    =
                                                                    let uu____3323
                                                                    =
                                                                    let uu____3332
                                                                    =
                                                                    let uu____3333
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3333
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3332,
                                                                    " ")  in
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
                                                                    let uu____3389
                                                                    =
                                                                    let uu____3398
                                                                    =
                                                                    let uu____3399
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3399
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____3398,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____3400
                                                                    =
                                                                    let uu____3411
                                                                    =
                                                                    let uu____3420
                                                                    =
                                                                    let uu____3421
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3421
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3420,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
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
                                                                    true  in
                                                                    Const
                                                                    uu____3454
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3453,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____3455
                                                                    =
                                                                    let uu____3466
                                                                    =
                                                                    let uu____3475
                                                                    =
                                                                    let uu____3476
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3476
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____3475,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____3477
                                                                    =
                                                                    let uu____3488
                                                                    =
                                                                    let uu____3497
                                                                    =
                                                                    let uu____3498
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3498
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3497,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____3499
                                                                    =
                                                                    let uu____3510
                                                                    =
                                                                    let uu____3519
                                                                    =
                                                                    let uu____3520
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3520
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____3519,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____3521
                                                                    =
                                                                    let uu____3532
                                                                    =
                                                                    let uu____3541
                                                                    =
                                                                    let uu____3542
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3542
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____3541,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____3543
                                                                    =
                                                                    let uu____3554
                                                                    =
                                                                    let uu____3563
                                                                    =
                                                                    let uu____3564
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3564
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____3563,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____3565
                                                                    =
                                                                    let uu____3576
                                                                    =
                                                                    let uu____3585
                                                                    =
                                                                    let uu____3586
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3586
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____3585,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____3587
                                                                    =
                                                                    let uu____3598
                                                                    =
                                                                    let uu____3607
                                                                    =
                                                                    let uu____3608
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3608
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____3607,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____3609
                                                                    =
                                                                    let uu____3620
                                                                    =
                                                                    let uu____3631
                                                                    =
                                                                    let uu____3640
                                                                    =
                                                                    let uu____3641
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3641
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____3640,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____3642
                                                                    =
                                                                    let uu____3653
                                                                    =
                                                                    let uu____3664
                                                                    =
                                                                    let uu____3675
                                                                    =
                                                                    let uu____3686
                                                                    =
                                                                    let uu____3695
                                                                    =
                                                                    let uu____3696
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3696
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____3695,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____3697
                                                                    =
                                                                    let uu____3708
                                                                    =
                                                                    let uu____3718
                                                                    =
                                                                    let uu____3719
                                                                    =
                                                                    let uu____3726
                                                                    =
                                                                    let uu____3727
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3727
                                                                     in
                                                                    ((fun
                                                                    uu____3732
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____3726)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____3719
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____3718,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____3736
                                                                    =
                                                                    let uu____3748
                                                                    =
                                                                    let uu____3757
                                                                    =
                                                                    let uu____3758
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3758
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____3757,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____3759
                                                                    =
                                                                    let uu____3770
                                                                    =
                                                                    let uu____3781
                                                                    =
                                                                    let uu____3790
                                                                    =
                                                                    let uu____3791
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3791
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____3790,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____3792
                                                                    =
                                                                    let uu____3803
                                                                    =
                                                                    let uu____3814
                                                                    =
                                                                    let uu____3825
                                                                    =
                                                                    let uu____3836
                                                                    =
                                                                    let uu____3847
                                                                    =
                                                                    let uu____3856
                                                                    =
                                                                    let uu____3857
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3857
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____3856,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____3858
                                                                    =
                                                                    let uu____3869
                                                                    =
                                                                    let uu____3878
                                                                    =
                                                                    let uu____3879
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3879
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____3878,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____3880
                                                                    =
                                                                    let uu____3891
                                                                    =
                                                                    let uu____3902
                                                                    =
                                                                    let uu____3911
                                                                    =
                                                                    let uu____3912
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3912
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    uu____3911,
                                                                    "Extract interfaces from the dependencies and use them for verification")
                                                                     in
                                                                    let uu____3913
                                                                    =
                                                                    let uu____3924
                                                                    =
                                                                    let uu____3934
                                                                    =
                                                                    let uu____3935
                                                                    =
                                                                    let uu____3942
                                                                    =
                                                                    let uu____3943
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3943
                                                                     in
                                                                    ((fun
                                                                    uu____3948
                                                                     ->
                                                                    (
                                                                    let uu____3950
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____3950);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____3942)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____3935
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____3934,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____3924]
                                                                     in
                                                                    uu____3902
                                                                    ::
                                                                    uu____3913
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____3891
                                                                     in
                                                                    uu____3869
                                                                    ::
                                                                    uu____3880
                                                                     in
                                                                    uu____3847
                                                                    ::
                                                                    uu____3858
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'false')")
                                                                    ::
                                                                    uu____3836
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____3825
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____3814
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____3803
                                                                     in
                                                                    uu____3781
                                                                    ::
                                                                    uu____3792
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____3770
                                                                     in
                                                                    uu____3748
                                                                    ::
                                                                    uu____3759
                                                                     in
                                                                    uu____3708
                                                                    ::
                                                                    uu____3736
                                                                     in
                                                                    uu____3686
                                                                    ::
                                                                    uu____3697
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____3675
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____3664
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____3653
                                                                     in
                                                                    uu____3631
                                                                    ::
                                                                    uu____3642
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____3620
                                                                     in
                                                                    uu____3598
                                                                    ::
                                                                    uu____3609
                                                                     in
                                                                    uu____3576
                                                                    ::
                                                                    uu____3587
                                                                     in
                                                                    uu____3554
                                                                    ::
                                                                    uu____3565
                                                                     in
                                                                    uu____3532
                                                                    ::
                                                                    uu____3543
                                                                     in
                                                                    uu____3510
                                                                    ::
                                                                    uu____3521
                                                                     in
                                                                    uu____3488
                                                                    ::
                                                                    uu____3499
                                                                     in
                                                                    uu____3466
                                                                    ::
                                                                    uu____3477
                                                                     in
                                                                    uu____3444
                                                                    ::
                                                                    uu____3455
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3433
                                                                     in
                                                                    uu____3411
                                                                    ::
                                                                    uu____3422
                                                                     in
                                                                    uu____3389
                                                                    ::
                                                                    uu____3400
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3378
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3367
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3356
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3345
                                                                     in
                                                                    uu____3323
                                                                    ::
                                                                    uu____3334
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3312
                                                                     in
                                                                    uu____3290
                                                                    ::
                                                                    uu____3301
                                                                     in
                                                                    uu____3268
                                                                    ::
                                                                    uu____3279
                                                                     in
                                                                    uu____3246
                                                                    ::
                                                                    uu____3257
                                                                     in
                                                                    uu____3224
                                                                    ::
                                                                    uu____3235
                                                                     in
                                                                    uu____3202
                                                                    ::
                                                                    uu____3213
                                                                     in
                                                                    uu____3180
                                                                    ::
                                                                    uu____3191
                                                                     in
                                                                    uu____3158
                                                                    ::
                                                                    uu____3169
                                                                     in
                                                                    uu____3136
                                                                    ::
                                                                    uu____3147
                                                                     in
                                                                    uu____3114
                                                                    ::
                                                                    uu____3125
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3103
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3092
                                                                     in
                                                                    uu____3070
                                                                    ::
                                                                    uu____3081
                                                                     in
                                                                    uu____3048
                                                                    ::
                                                                    uu____3059
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3037
                                                                     in
                                                                    uu____3015
                                                                    ::
                                                                    uu____3026
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3004
                                                                     in
                                                                    uu____2982
                                                                    ::
                                                                    uu____2993
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____2971
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____2960
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____2949
                                                                     in
                                                                    uu____2927
                                                                    ::
                                                                    uu____2938
                                                                     in
                                                                  uu____2905
                                                                    ::
                                                                    uu____2916
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "load",
                                                                  (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                  "Load compiled module")
                                                                  ::
                                                                  uu____2894
                                                                 in
                                                              uu____2872 ::
                                                                uu____2883
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "initial_ifuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                              :: uu____2861
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "initial_fuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of recursive functions to try initially (default 2)")
                                                            :: uu____2850
                                                           in
                                                        uu____2828 ::
                                                          uu____2839
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "include",
                                                        (ReverseAccumulated
                                                           (PathStr "path")),
                                                        "A directory in which to search for files included on the command line")
                                                        :: uu____2817
                                                       in
                                                    uu____2795 :: uu____2806
                                                     in
                                                  uu____2773 :: uu____2784
                                                   in
                                                uu____2751 :: uu____2762  in
                                              (FStar_Getopt.noshort,
                                                "hint_file",
                                                (PathStr "path"),
                                                "Read/write hints to <path> (instead of module-specific hints files)")
                                                :: uu____2740
                                               in
                                            uu____2718 :: uu____2729  in
                                          (FStar_Getopt.noshort,
                                            "fstar_home", (PathStr "dir"),
                                            "Set the FSTAR_HOME variable to <dir>")
                                            :: uu____2707
                                           in
                                        uu____2685 :: uu____2696  in
                                      (FStar_Getopt.noshort,
                                        "extract_namespace",
                                        (Accumulated
                                           (PostProcessed
                                              (pp_lowercase,
                                                (SimpleStr "namespace name")))),
                                        "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                        :: uu____2674
                                       in
                                    (FStar_Getopt.noshort, "extract_module",
                                      (Accumulated
                                         (PostProcessed
                                            (pp_lowercase,
                                              (SimpleStr "module_name")))),
                                      "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                      :: uu____2663
                                     in
                                  (FStar_Getopt.noshort, "extract",
                                    (Accumulated
                                       (SimpleStr
                                          "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                    "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                    :: uu____2652
                                   in
                                uu____2630 :: uu____2641  in
                              (FStar_Getopt.noshort, "dump_module",
                                (Accumulated (SimpleStr "module_name")), "")
                                :: uu____2619
                               in
                            uu____2597 :: uu____2608  in
                          uu____2575 :: uu____2586  in
                        uu____2553 :: uu____2564  in
                      (FStar_Getopt.noshort, "dep",
                        (EnumStr ["make"; "graph"; "full"]),
                        "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                        :: uu____2542
                       in
                    (FStar_Getopt.noshort, "defensive",
                      (EnumStr ["no"; "warn"; "fail"]),
                      "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                      :: uu____2531
                     in
                  (FStar_Getopt.noshort, "debug_level",
                    (Accumulated
                       (OpenEnumStr
                          (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                    "Control the verbosity of debugging info") :: uu____2520
                   in
                (FStar_Getopt.noshort, "debug",
                  (Accumulated (SimpleStr "module_name")),
                  "Print lots of debugging information while checking module")
                  :: uu____2509
                 in
              (FStar_Getopt.noshort, "codegen-lib",
                (Accumulated (SimpleStr "namespace")),
                "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                :: uu____2498
               in
            (FStar_Getopt.noshort, "codegen",
              (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
              "Generate code for further compilation to executable code, or build a compiler plugin")
              :: uu____2487
             in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2476
           in
        uu____2454 :: uu____2465  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2443
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2432

and (specs : Prims.unit -> FStar_Getopt.opt Prims.list) =
  fun uu____4698  ->
    let uu____4701 = specs_with_types ()  in
    FStar_List.map
      (fun uu____4726  ->
         match uu____4726 with
         | (short,long,typ,doc) ->
             let uu____4739 =
               let uu____4750 = arg_spec_of_opt_type long typ  in
               (short, long, uu____4750, doc)  in
             mk_spec uu____4739) uu____4701

let (settable : Prims.string -> Prims.bool) =
  fun uu___42_4757  ->
    match uu___42_4757 with
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
    | uu____4758 -> false
  
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
       (fun uu____4815  ->
          match uu____4815 with
          | (uu____4826,x,uu____4828,uu____4829) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,Prims.unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____4875  ->
          match uu____4875 with
          | (uu____4886,x,uu____4888,uu____4889) -> resettable x))
  
let (display_usage : Prims.unit -> Prims.unit) =
  fun uu____4896  ->
    let uu____4897 = specs ()  in display_usage_aux uu____4897
  
let (fstar_home : Prims.unit -> Prims.string) =
  fun uu____4912  ->
    let uu____4913 = get_fstar_home ()  in
    match uu____4913 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir ()  in
        let x1 = Prims.strcat x "/.."  in
        ((let uu____4919 =
            let uu____4924 = mk_string x1  in ("fstar_home", uu____4924)  in
          set_option' uu____4919);
         x1)
    | FStar_Pervasives_Native.Some x -> x
  
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____4932 -> true
    | uu____4933 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____4940 -> uu____4940
  
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
          let uu____4984 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____4984
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5010  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5015 =
             let uu____5018 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5018 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5015)
       in
    let uu____5067 =
      let uu____5070 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5070
       in
    (res, uu____5067)
  
let (file_list : Prims.unit -> Prims.string Prims.list) =
  fun uu____5102  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____5135 = specs ()  in
       FStar_Getopt.parse_cmdline uu____5135 (fun x  -> ())  in
     (let uu____5141 =
        let uu____5146 =
          let uu____5147 = FStar_List.map mk_string old_verify_module  in
          List uu____5147  in
        ("verify_module", uu____5146)  in
      set_option' uu____5141);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____5155 =
        let uu____5156 =
          let uu____5157 =
            let uu____5158 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____5158  in
          (FStar_String.length f1) - uu____5157  in
        uu____5156 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5155  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5162 = get_lax ()  in
    if uu____5162
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____5170 = module_name_of_file_name fn  in should_verify uu____5170
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5174 = get___temp_no_proj ()  in
    FStar_List.contains m uu____5174
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5180 = should_verify m  in
    if uu____5180 then m <> "Prims" else false
  
let (include_path : Prims.unit -> Prims.string Prims.list) =
  fun uu____5186  ->
    let uu____5187 = get_no_default_includes ()  in
    if uu____5187
    then get_include ()
    else
      (let h = fstar_home ()  in
       let defs = universe_include_path_base_dirs  in
       let uu____5195 =
         let uu____5198 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x))
            in
         FStar_All.pipe_right uu____5198
           (FStar_List.filter FStar_Util.file_exists)
          in
       let uu____5211 =
         let uu____5214 = get_include ()  in
         FStar_List.append uu____5214 ["."]  in
       FStar_List.append uu____5195 uu____5211)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun filename  ->
    let uu____5222 = FStar_Util.is_path_absolute filename  in
    if uu____5222
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5229 =
         let uu____5232 = include_path ()  in FStar_List.rev uu____5232  in
       FStar_Util.find_map uu____5229
         (fun p  ->
            let path =
              if p = "." then filename else FStar_Util.join_paths p filename
               in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
  
let (prims : Prims.unit -> Prims.string) =
  fun uu____5245  ->
    let uu____5246 = get_prims ()  in
    match uu____5246 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____5250 = find_file filename  in
        (match uu____5250 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5254 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____5254)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : Prims.unit -> Prims.string) =
  fun uu____5258  ->
    let uu____5259 = prims ()  in FStar_Util.basename uu____5259
  
let (pervasives : Prims.unit -> Prims.string) =
  fun uu____5262  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____5264 = find_file filename  in
    match uu____5264 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5268 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5268
  
let (pervasives_basename : Prims.unit -> Prims.string) =
  fun uu____5271  ->
    let uu____5272 = pervasives ()  in FStar_Util.basename uu____5272
  
let (pervasives_native_basename : Prims.unit -> Prims.string) =
  fun uu____5275  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____5277 = find_file filename  in
    match uu____5277 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5281 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5281
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____5285 = get_odir ()  in
    match uu____5285 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____5292 = get_cache_dir ()  in
    match uu____5292 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____5296 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____5296
  
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
             let uu____5348 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             FStar_Ident.path_of_text uu____5348  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((FStar_Ident.path_of_text s1), true))
       in
    let uu____5356 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____5356 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____5424 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____5424 (FStar_List.contains s)
  
let (__temp_fast_implicits : Prims.unit -> Prims.bool) =
  fun uu____5431  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : Prims.unit -> Prims.bool) =
  fun uu____5434  -> get_admit_smt_queries () 
let (admit_except :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5439  -> get_admit_except () 
let (cache_checked_modules : Prims.unit -> Prims.bool) =
  fun uu____5442  -> get_cache_checked_modules () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin [@@deriving show]
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____5446 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____5450 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____5454 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____5458 -> false
  
let (codegen : Prims.unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____5463  ->
    let uu____5464 = get_codegen ()  in
    FStar_Util.map_opt uu____5464
      (fun uu___43_5468  ->
         match uu___43_5468 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____5469 -> failwith "Impossible")
  
let (codegen_libs : Prims.unit -> Prims.string Prims.list Prims.list) =
  fun uu____5476  ->
    let uu____5477 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____5477
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : Prims.unit -> Prims.bool) =
  fun uu____5492  -> let uu____5493 = get_debug ()  in uu____5493 <> [] 
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____5506 = get_debug ()  in
       FStar_All.pipe_right uu____5506 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : Prims.unit -> Prims.bool) =
  fun uu____5513  -> let uu____5514 = get_defensive ()  in uu____5514 <> "no" 
let (defensive_fail : Prims.unit -> Prims.bool) =
  fun uu____5517  ->
    let uu____5518 = get_defensive ()  in uu____5518 = "fail"
  
let (dep : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5523  -> get_dep () 
let (detail_errors : Prims.unit -> Prims.bool) =
  fun uu____5526  -> get_detail_errors () 
let (detail_hint_replay : Prims.unit -> Prims.bool) =
  fun uu____5529  -> get_detail_hint_replay () 
let (doc : Prims.unit -> Prims.bool) = fun uu____5532  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____5536 = get_dump_module ()  in
    FStar_All.pipe_right uu____5536 (FStar_List.contains s)
  
let (eager_inference : Prims.unit -> Prims.bool) =
  fun uu____5543  -> get_eager_inference () 
let (expose_interfaces : Prims.unit -> Prims.bool) =
  fun uu____5546  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____5550 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____5550
  
let (full_context_dependency : Prims.unit -> Prims.bool) =
  fun uu____5578  -> true 
let (hide_uvar_nums : Prims.unit -> Prims.bool) =
  fun uu____5581  -> get_hide_uvar_nums () 
let (hint_info : Prims.unit -> Prims.bool) =
  fun uu____5584  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5589  -> get_hint_file () 
let (ide : Prims.unit -> Prims.bool) = fun uu____5592  -> get_ide () 
let (indent : Prims.unit -> Prims.bool) = fun uu____5595  -> get_indent () 
let (initial_fuel : Prims.unit -> Prims.int) =
  fun uu____5598  ->
    let uu____5599 = get_initial_fuel ()  in
    let uu____5600 = get_max_fuel ()  in Prims.min uu____5599 uu____5600
  
let (initial_ifuel : Prims.unit -> Prims.int) =
  fun uu____5603  ->
    let uu____5604 = get_initial_ifuel ()  in
    let uu____5605 = get_max_ifuel ()  in Prims.min uu____5604 uu____5605
  
let (interactive : Prims.unit -> Prims.bool) =
  fun uu____5608  -> (get_in ()) || (get_ide ()) 
let (lax : Prims.unit -> Prims.bool) = fun uu____5611  -> get_lax () 
let (load : Prims.unit -> Prims.string Prims.list) =
  fun uu____5616  -> get_load () 
let (legacy_interactive : Prims.unit -> Prims.bool) =
  fun uu____5619  -> get_in () 
let (log_queries : Prims.unit -> Prims.bool) =
  fun uu____5622  -> get_log_queries () 
let (log_types : Prims.unit -> Prims.bool) =
  fun uu____5625  -> get_log_types () 
let (max_fuel : Prims.unit -> Prims.int) = fun uu____5628  -> get_max_fuel () 
let (max_ifuel : Prims.unit -> Prims.int) =
  fun uu____5631  -> get_max_ifuel () 
let (min_fuel : Prims.unit -> Prims.int) = fun uu____5634  -> get_min_fuel () 
let (ml_ish : Prims.unit -> Prims.bool) = fun uu____5637  -> get_MLish () 
let (set_ml_ish : Prims.unit -> Prims.unit) =
  fun uu____5640  -> set_option "MLish" (Bool true) 
let (n_cores : Prims.unit -> Prims.int) = fun uu____5643  -> get_n_cores () 
let (no_default_includes : Prims.unit -> Prims.bool) =
  fun uu____5646  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____5651 = get_no_extract ()  in
    FStar_All.pipe_right uu____5651
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : Prims.unit -> Prims.bool) =
  fun uu____5660  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : Prims.unit -> Prims.bool) =
  fun uu____5663  -> get_no_location_info () 
let (output_dir : Prims.unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____5668  -> get_odir () 
let (ugly : Prims.unit -> Prims.bool) = fun uu____5671  -> get_ugly () 
let (print_bound_var_types : Prims.unit -> Prims.bool) =
  fun uu____5674  -> get_print_bound_var_types () 
let (print_effect_args : Prims.unit -> Prims.bool) =
  fun uu____5677  -> get_print_effect_args () 
let (print_implicits : Prims.unit -> Prims.bool) =
  fun uu____5680  -> get_print_implicits () 
let (print_real_names : Prims.unit -> Prims.bool) =
  fun uu____5683  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : Prims.unit -> Prims.bool) =
  fun uu____5686  -> get_print_universes () 
let (print_z3_statistics : Prims.unit -> Prims.bool) =
  fun uu____5689  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : Prims.unit -> Prims.bool) =
  fun uu____5692  -> get_query_stats () 
let (record_hints : Prims.unit -> Prims.bool) =
  fun uu____5695  -> get_record_hints () 
let (reuse_hint_for :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5700  -> get_reuse_hint_for () 
let (silent : Prims.unit -> Prims.bool) = fun uu____5703  -> get_silent () 
let (smtencoding_elim_box : Prims.unit -> Prims.bool) =
  fun uu____5706  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : Prims.unit -> Prims.bool) =
  fun uu____5709  ->
    let uu____5710 = get_smtencoding_nl_arith_repr ()  in
    uu____5710 = "native"
  
let (smtencoding_nl_arith_wrapped : Prims.unit -> Prims.bool) =
  fun uu____5713  ->
    let uu____5714 = get_smtencoding_nl_arith_repr ()  in
    uu____5714 = "wrapped"
  
let (smtencoding_nl_arith_default : Prims.unit -> Prims.bool) =
  fun uu____5717  ->
    let uu____5718 = get_smtencoding_nl_arith_repr ()  in
    uu____5718 = "boxwrap"
  
let (smtencoding_l_arith_native : Prims.unit -> Prims.bool) =
  fun uu____5721  ->
    let uu____5722 = get_smtencoding_l_arith_repr ()  in
    uu____5722 = "native"
  
let (smtencoding_l_arith_default : Prims.unit -> Prims.bool) =
  fun uu____5725  ->
    let uu____5726 = get_smtencoding_l_arith_repr ()  in
    uu____5726 = "boxwrap"
  
let (tactic_raw_binders : Prims.unit -> Prims.bool) =
  fun uu____5729  -> get_tactic_raw_binders () 
let (tactic_trace : Prims.unit -> Prims.bool) =
  fun uu____5732  -> get_tactic_trace () 
let (tactic_trace_d : Prims.unit -> Prims.int) =
  fun uu____5735  -> get_tactic_trace_d () 
let (timing : Prims.unit -> Prims.bool) = fun uu____5738  -> get_timing () 
let (trace_error : Prims.unit -> Prims.bool) =
  fun uu____5741  -> get_trace_error () 
let (unthrottle_inductives : Prims.unit -> Prims.bool) =
  fun uu____5744  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : Prims.unit -> Prims.bool) =
  fun uu____5747  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : Prims.unit -> Prims.bool) =
  fun uu____5750  -> get_use_eq_at_higher_order () 
let (use_hints : Prims.unit -> Prims.bool) =
  fun uu____5753  -> get_use_hints () 
let (use_hint_hashes : Prims.unit -> Prims.bool) =
  fun uu____5756  -> get_use_hint_hashes () 
let (use_native_tactics :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____5761  -> get_use_native_tactics () 
let (use_tactics : Prims.unit -> Prims.bool) =
  fun uu____5764  -> get_use_tactics () 
let (using_facts_from :
  Prims.unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____5773  ->
    let uu____5774 = get_using_facts_from ()  in
    match uu____5774 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : Prims.unit -> Prims.bool) =
  fun uu____5808  ->
    let uu____5809 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____5809
  
let (vcgen_decorate_with_type : Prims.unit -> Prims.bool) =
  fun uu____5814  ->
    let uu____5815 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____5815 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____5818 -> false
  
let (warn_default_effects : Prims.unit -> Prims.bool) =
  fun uu____5823  -> get_warn_default_effects () 
let (z3_exe : Prims.unit -> Prims.string) =
  fun uu____5826  ->
    let uu____5827 = get_smt ()  in
    match uu____5827 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : Prims.unit -> Prims.string Prims.list) =
  fun uu____5835  -> get_z3cliopt () 
let (z3_refresh : Prims.unit -> Prims.bool) =
  fun uu____5838  -> get_z3refresh () 
let (z3_rlimit : Prims.unit -> Prims.int) =
  fun uu____5841  -> get_z3rlimit () 
let (z3_rlimit_factor : Prims.unit -> Prims.int) =
  fun uu____5844  -> get_z3rlimit_factor () 
let (z3_seed : Prims.unit -> Prims.int) = fun uu____5847  -> get_z3seed () 
let (use_two_phase_tc : Prims.unit -> Prims.bool) =
  fun uu____5850  -> get_use_two_phase_tc () 
let (no_positivity : Prims.unit -> Prims.bool) =
  fun uu____5853  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : Prims.unit -> Prims.bool) =
  fun uu____5856  -> get_ml_no_eta_expand_coertions () 
let (warn_error : Prims.unit -> Prims.string) =
  fun uu____5859  -> get_warn_error () 
let (use_extracted_interfaces : Prims.unit -> Prims.bool) =
  fun uu____5862  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____5867 = get_extract ()  in
    match uu____5867 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____5878 =
            let uu____5891 = get_no_extract ()  in
            let uu____5894 = get_extract_namespace ()  in
            let uu____5897 = get_extract_module ()  in
            (uu____5891, uu____5894, uu____5897)  in
          match uu____5878 with
          | ([],[],[]) -> ()
          | uu____5912 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = FStar_Ident.path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____5956,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____5975 -> false  in
          let uu____5984 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____6018  ->
                    match uu____6018 with
                    | (path,uu____6026) -> matches_path m_components path))
             in
          match uu____5984 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____6037,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____6055 = get_extract_namespace ()  in
          match uu____6055 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____6069 = get_extract_module ()  in
          match uu____6069 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____6081 = no_extract m1  in Prims.op_Negation uu____6081) &&
          (let uu____6083 =
             let uu____6092 = get_extract_namespace ()  in
             let uu____6095 = get_extract_module ()  in
             (uu____6092, uu____6095)  in
           (match uu____6083 with
            | ([],[]) -> true
            | uu____6106 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  