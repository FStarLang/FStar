open Prims
type debug_level_t =
  | Low 
  | Medium 
  | High 
  | Extreme 
  | Other of Prims.string 
let (uu___is_Low : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | Low  -> true | uu____11 -> false 
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____17 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | High  -> true | uu____23 -> false 
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____29 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____36 -> false
  
let (__proj__Other__item___0 : debug_level_t -> Prims.string) =
  fun projectee  -> match projectee with | Other _0 -> _0 
type option_val =
  | Bool of Prims.bool 
  | String of Prims.string 
  | Path of Prims.string 
  | Int of Prims.int 
  | List of option_val Prims.list 
  | Unset 
let (uu___is_Bool : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____77 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____91 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____105 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____119 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____135 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____154 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _0_4  -> Bool _0_4 
let (mk_string : Prims.string -> option_val) = fun _0_5  -> String _0_5 
let (mk_path : Prims.string -> option_val) = fun _0_6  -> Path _0_6 
let (mk_int : Prims.int -> option_val) = fun _0_7  -> Int _0_7 
let (mk_list : option_val Prims.list -> option_val) = fun _0_8  -> List _0_8 
type options =
  | Set 
  | Reset 
  | Restore 
let (uu___is_Set : options -> Prims.bool) =
  fun projectee  -> match projectee with | Set  -> true | uu____182 -> false 
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____188 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____194 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____212  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____240  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____268  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___73_296  ->
    match uu___73_296 with
    | Bool b -> b
    | uu____298 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___74_303  ->
    match uu___74_303 with
    | Int b -> b
    | uu____305 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___75_310  ->
    match uu___75_310 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____313 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___76_320  ->
    match uu___76_320 with
    | List ts -> ts
    | uu____326 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____335 .
    (option_val -> 'Auu____335) -> option_val -> 'Auu____335 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____353 = as_list' x  in
      FStar_All.pipe_right uu____353 (FStar_List.map as_t)
  
let as_option :
  'Auu____366 .
    (option_val -> 'Auu____366) ->
      option_val -> 'Auu____366 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___77_381  ->
      match uu___77_381 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____385 = as_t v1  in FStar_Pervasives_Native.Some uu____385
  
type optionstate = option_val FStar_Util.smap
let (fstar_options : optionstate Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : unit -> optionstate) =
  fun uu____409  ->
    let uu____410 = FStar_ST.op_Bang fstar_options  in
    FStar_List.hd uu____410
  
let (pop : unit -> unit) =
  fun uu____444  ->
    let uu____445 = FStar_ST.op_Bang fstar_options  in
    match uu____445 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____475::[] -> failwith "TOO MANY POPS!"
    | uu____476::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____511  ->
    let uu____512 =
      let uu____515 =
        let uu____516 = peek ()  in FStar_Util.smap_copy uu____516  in
      let uu____519 = FStar_ST.op_Bang fstar_options  in uu____515 ::
        uu____519
       in
    FStar_ST.op_Colon_Equals fstar_options uu____512
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____581 = FStar_ST.op_Bang fstar_options  in
    match uu____581 with
    | [] -> failwith "set on empty option stack"
    | uu____611::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
  
let (snapshot : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____650  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  -> let uu____670 = peek ()  in FStar_Util.smap_add uu____670 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____681  -> match uu____681 with | (k,v1) -> set_option k v1 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f ()  in pop (); retv) 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____728 =
      let uu____731 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____731
       in
    FStar_ST.op_Colon_Equals light_off_files uu____728
  
let (defaults :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 Prims.list) =
  [("__temp_no_proj", (List []));
  ("__temp_fast_implicits", (Bool false));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
  ("cache_checked_modules", (Bool false));
  ("cache_dir", Unset);
  ("cache_off", (Bool false));
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
  ("eager_subtyping", (Bool false));
  ("expose_interfaces", (Bool false));
  ("extract", Unset);
  ("extract_all", (Bool false));
  ("extract_module", (List []));
  ("extract_namespace", (List []));
  ("fs_typ_app", (Bool false));
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
  ("integer_overloading", (Bool false));
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
  ("use_two_phase_tc", (Bool true));
  ("__no_positivity", (Bool false));
  ("__ml_no_eta_expand_coertions", (Bool false));
  ("warn_error", (String ""));
  ("use_extracted_interfaces", (Bool false))] 
let (init : unit -> unit) =
  fun uu____1186  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1203  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1268 =
      let uu____1271 = peek ()  in FStar_Util.smap_try_find uu____1271 s  in
    match uu____1268 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1281 . Prims.string -> (option_val -> 'Auu____1281) -> 'Auu____1281
  = fun s  -> fun c  -> let uu____1297 = get_option s  in c uu____1297 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1302  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1309  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1316  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1323  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1330  -> lookup_opt "cache_off" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1337  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1346  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1355  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1364  -> lookup_opt "debug_level" (as_list as_string) 
let (get_defensive : unit -> Prims.string) =
  fun uu____1371  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1378  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1385  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1390  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1395  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1402  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1409  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1414  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1423  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1436  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1445  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1452  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1457  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1462  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1469  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1476  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1481  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1488  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1495  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1500  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1505  -> lookup_opt "initial_ifuel" as_int 
let (get_integer_overloading : unit -> Prims.bool) =
  fun uu____1510  -> lookup_opt "integer_overloading" as_bool 
let (get_lax : unit -> Prims.bool) =
  fun uu____1515  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1522  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1529  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1534  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1539  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1544  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1549  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1554  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1559  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1564  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1571  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1578  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1583  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1588  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1595  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1602  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1609  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1616  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1621  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1626  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1631  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1636  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1641  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1646  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1651  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1656  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1663  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1670  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1677  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1684  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1689  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1694  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1699  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1704  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1709  -> lookup_opt "tactic_trace_d" as_int 
let (get_timing : unit -> Prims.bool) =
  fun uu____1714  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1719  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1724  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1729  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1734  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1739  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1744  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1751  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1758  ->
    let uu____1759 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1759
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1768  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1781  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1790  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1799  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1806  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1811  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1818  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1825  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1830  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1835  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1840  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1845  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1850  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1855  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1860  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1865  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___78_1870  ->
    match uu___78_1870 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1882 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1888 = get_debug_level ()  in
    FStar_All.pipe_right uu____1888
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2021  ->
    let uu____2022 =
      let uu____2023 = FStar_ST.op_Bang _version  in
      let uu____2047 = FStar_ST.op_Bang _platform  in
      let uu____2071 = FStar_ST.op_Bang _compiler  in
      let uu____2095 = FStar_ST.op_Bang _date  in
      let uu____2119 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2023
        uu____2047 uu____2071 uu____2095 uu____2119
       in
    FStar_Util.print_string uu____2022
  
let display_usage_aux :
  'Auu____2149 'Auu____2150 .
    ('Auu____2149,Prims.string,'Auu____2150 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2198  ->
         match uu____2198 with
         | (uu____2209,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2221 =
                      let uu____2222 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2222  in
                    FStar_Util.print_string uu____2221
                  else
                    (let uu____2224 =
                       let uu____2225 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2225 doc  in
                     FStar_Util.print_string uu____2224)
              | FStar_Getopt.OneArg (uu____2226,argname) ->
                  if doc = ""
                  then
                    let uu____2234 =
                      let uu____2235 = FStar_Util.colorize_bold flag  in
                      let uu____2236 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2235 uu____2236
                       in
                    FStar_Util.print_string uu____2234
                  else
                    (let uu____2238 =
                       let uu____2239 = FStar_Util.colorize_bold flag  in
                       let uu____2240 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2239
                         uu____2240 doc
                        in
                     FStar_Util.print_string uu____2238))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2268 = o  in
    match uu____2268 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2304 =
                let uu____2305 = f ()  in set_option name uu____2305  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2320 = f x  in set_option name uu____2320
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2340 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2340  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2363 =
        let uu____2366 = lookup_opt name as_list'  in
        FStar_List.append uu____2366 [value]  in
      mk_list uu____2363
  
let accumulate_string :
  'Auu____2379 .
    Prims.string -> ('Auu____2379 -> Prims.string) -> 'Auu____2379 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2400 =
          let uu____2401 =
            let uu____2402 = post_processor value  in mk_string uu____2402
             in
          accumulated_option name uu____2401  in
        set_option name uu____2400
  
let (add_extract_module : Prims.string -> unit) =
  fun s  -> accumulate_string "extract_module" FStar_String.lowercase s 
let (add_extract_namespace : Prims.string -> unit) =
  fun s  -> accumulate_string "extract_namespace" FStar_String.lowercase s 
let (add_verify_module : Prims.string -> unit) =
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
  | WithSideEffect of (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2 
let (uu___is_Const : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____2498 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2512 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2525 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2532 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2546 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2562 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2588 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2627 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2662 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2676 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2697 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2735 -> true
    | uu____2736 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2743 -> uu____2743
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2763 ->
              let uu____2764 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2764 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2768 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2768
          | PathStr uu____2771 -> mk_path str_val
          | SimpleStr uu____2772 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2777 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2792 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2792
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
            let uu____2811 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2811
  
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
    | PostProcessed (uu____2848,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2858,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2885 = desc_of_opt_type typ  in
      match uu____2885 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2891  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2908 =
      let uu____2909 = as_string s  in FStar_String.lowercase uu____2909  in
    mk_string uu____2908
  
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2931  ->
    let uu____2943 =
      let uu____2955 =
        let uu____2967 =
          let uu____2977 = let uu____2978 = mk_bool true  in Const uu____2978
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2977,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
           in
        let uu____2980 =
          let uu____2992 =
            let uu____3004 =
              let uu____3014 =
                let uu____3015 = mk_bool true  in Const uu____3015  in
              (FStar_Getopt.noshort, "cache_off", uu____3014,
                "Do not read or write any .checked files")
               in
            let uu____3017 =
              let uu____3029 =
                let uu____3041 =
                  let uu____3053 =
                    let uu____3065 =
                      let uu____3077 =
                        let uu____3089 =
                          let uu____3101 =
                            let uu____3111 =
                              let uu____3112 = mk_bool true  in
                              Const uu____3112  in
                            (FStar_Getopt.noshort, "detail_errors",
                              uu____3111,
                              "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                             in
                          let uu____3114 =
                            let uu____3126 =
                              let uu____3136 =
                                let uu____3137 = mk_bool true  in
                                Const uu____3137  in
                              (FStar_Getopt.noshort, "detail_hint_replay",
                                uu____3136,
                                "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                               in
                            let uu____3139 =
                              let uu____3151 =
                                let uu____3161 =
                                  let uu____3162 = mk_bool true  in
                                  Const uu____3162  in
                                (FStar_Getopt.noshort, "doc", uu____3161,
                                  "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                 in
                              let uu____3164 =
                                let uu____3176 =
                                  let uu____3188 =
                                    let uu____3198 =
                                      let uu____3199 = mk_bool true  in
                                      Const uu____3199  in
                                    (FStar_Getopt.noshort, "eager_inference",
                                      uu____3198,
                                      "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                     in
                                  let uu____3201 =
                                    let uu____3213 =
                                      let uu____3223 =
                                        let uu____3224 = mk_bool true  in
                                        Const uu____3224  in
                                      (FStar_Getopt.noshort,
                                        "eager_subtyping", uu____3223,
                                        "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                       in
                                    let uu____3226 =
                                      let uu____3238 =
                                        let uu____3250 =
                                          let uu____3262 =
                                            let uu____3274 =
                                              let uu____3284 =
                                                let uu____3285 = mk_bool true
                                                   in
                                                Const uu____3285  in
                                              (FStar_Getopt.noshort,
                                                "expose_interfaces",
                                                uu____3284,
                                                "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                               in
                                            let uu____3287 =
                                              let uu____3299 =
                                                let uu____3309 =
                                                  let uu____3310 =
                                                    mk_bool true  in
                                                  Const uu____3310  in
                                                (FStar_Getopt.noshort,
                                                  "hide_uvar_nums",
                                                  uu____3309,
                                                  "Don't print unification variable numbers")
                                                 in
                                              let uu____3312 =
                                                let uu____3324 =
                                                  let uu____3336 =
                                                    let uu____3346 =
                                                      let uu____3347 =
                                                        mk_bool true  in
                                                      Const uu____3347  in
                                                    (FStar_Getopt.noshort,
                                                      "hint_info",
                                                      uu____3346,
                                                      "Print information regarding hints (deprecated; use --query_stats instead)")
                                                     in
                                                  let uu____3349 =
                                                    let uu____3361 =
                                                      let uu____3371 =
                                                        let uu____3372 =
                                                          mk_bool true  in
                                                        Const uu____3372  in
                                                      (FStar_Getopt.noshort,
                                                        "in", uu____3371,
                                                        "Legacy interactive mode; reads input from stdin")
                                                       in
                                                    let uu____3374 =
                                                      let uu____3386 =
                                                        let uu____3396 =
                                                          let uu____3397 =
                                                            mk_bool true  in
                                                          Const uu____3397
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "ide", uu____3396,
                                                          "JSON-based interactive mode for IDEs")
                                                         in
                                                      let uu____3399 =
                                                        let uu____3411 =
                                                          let uu____3423 =
                                                            let uu____3433 =
                                                              let uu____3434
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____3434
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "indent",
                                                              uu____3433,
                                                              "Parses and outputs the files on the command line")
                                                             in
                                                          let uu____3436 =
                                                            let uu____3448 =
                                                              let uu____3460
                                                                =
                                                                let uu____3472
                                                                  =
                                                                  let uu____3484
                                                                    =
                                                                    let uu____3494
                                                                    =
                                                                    let uu____3495
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3495
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3494,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                  let uu____3497
                                                                    =
                                                                    let uu____3509
                                                                    =
                                                                    let uu____3521
                                                                    =
                                                                    let uu____3531
                                                                    =
                                                                    let uu____3532
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3532
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3531,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3534
                                                                    =
                                                                    let uu____3546
                                                                    =
                                                                    let uu____3556
                                                                    =
                                                                    let uu____3557
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3557
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3556,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3559
                                                                    =
                                                                    let uu____3571
                                                                    =
                                                                    let uu____3583
                                                                    =
                                                                    let uu____3595
                                                                    =
                                                                    let uu____3607
                                                                    =
                                                                    let uu____3617
                                                                    =
                                                                    let uu____3618
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3618
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3617,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3620
                                                                    =
                                                                    let uu____3632
                                                                    =
                                                                    let uu____3644
                                                                    =
                                                                    let uu____3654
                                                                    =
                                                                    let uu____3655
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3655
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3654,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3657
                                                                    =
                                                                    let uu____3669
                                                                    =
                                                                    let uu____3681
                                                                    =
                                                                    let uu____3691
                                                                    =
                                                                    let uu____3692
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3692
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3691,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3694
                                                                    =
                                                                    let uu____3706
                                                                    =
                                                                    let uu____3716
                                                                    =
                                                                    let uu____3717
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3717
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3716,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3719
                                                                    =
                                                                    let uu____3731
                                                                    =
                                                                    let uu____3741
                                                                    =
                                                                    let uu____3742
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3742
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3741,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3744
                                                                    =
                                                                    let uu____3756
                                                                    =
                                                                    let uu____3768
                                                                    =
                                                                    let uu____3780
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
                                                                    "print_bound_var_types",
                                                                    uu____3790,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3793
                                                                    =
                                                                    let uu____3805
                                                                    =
                                                                    let uu____3815
                                                                    =
                                                                    let uu____3816
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3816
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3815,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3818
                                                                    =
                                                                    let uu____3830
                                                                    =
                                                                    let uu____3840
                                                                    =
                                                                    let uu____3841
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3841
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3840,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3843
                                                                    =
                                                                    let uu____3855
                                                                    =
                                                                    let uu____3865
                                                                    =
                                                                    let uu____3866
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3866
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3865,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3868
                                                                    =
                                                                    let uu____3880
                                                                    =
                                                                    let uu____3890
                                                                    =
                                                                    let uu____3891
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3891
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3890,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3893
                                                                    =
                                                                    let uu____3905
                                                                    =
                                                                    let uu____3915
                                                                    =
                                                                    let uu____3916
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3916
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3915,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3918
                                                                    =
                                                                    let uu____3930
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
                                                                    "prn",
                                                                    uu____3940,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3943
                                                                    =
                                                                    let uu____3955
                                                                    =
                                                                    let uu____3965
                                                                    =
                                                                    let uu____3966
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3966
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3965,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3968
                                                                    =
                                                                    let uu____3980
                                                                    =
                                                                    let uu____3990
                                                                    =
                                                                    let uu____3991
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3991
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3990,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3993
                                                                    =
                                                                    let uu____4005
                                                                    =
                                                                    let uu____4017
                                                                    =
                                                                    let uu____4027
                                                                    =
                                                                    let uu____4028
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4028
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4027,
                                                                    " ")  in
                                                                    let uu____4030
                                                                    =
                                                                    let uu____4042
                                                                    =
                                                                    let uu____4054
                                                                    =
                                                                    let uu____4066
                                                                    =
                                                                    let uu____4078
                                                                    =
                                                                    let uu____4090
                                                                    =
                                                                    let uu____4100
                                                                    =
                                                                    let uu____4101
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4101
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4100,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4103
                                                                    =
                                                                    let uu____4115
                                                                    =
                                                                    let uu____4125
                                                                    =
                                                                    let uu____4126
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4126
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4125,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4128
                                                                    =
                                                                    let uu____4140
                                                                    =
                                                                    let uu____4152
                                                                    =
                                                                    let uu____4162
                                                                    =
                                                                    let uu____4163
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4163
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4162,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4165
                                                                    =
                                                                    let uu____4177
                                                                    =
                                                                    let uu____4187
                                                                    =
                                                                    let uu____4188
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4188
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4187,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4190
                                                                    =
                                                                    let uu____4202
                                                                    =
                                                                    let uu____4212
                                                                    =
                                                                    let uu____4213
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4213
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4212,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4215
                                                                    =
                                                                    let uu____4227
                                                                    =
                                                                    let uu____4237
                                                                    =
                                                                    let uu____4238
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4238
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4237,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4240
                                                                    =
                                                                    let uu____4252
                                                                    =
                                                                    let uu____4262
                                                                    =
                                                                    let uu____4263
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4263
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4262,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4265
                                                                    =
                                                                    let uu____4277
                                                                    =
                                                                    let uu____4287
                                                                    =
                                                                    let uu____4288
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4288
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4287,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4290
                                                                    =
                                                                    let uu____4302
                                                                    =
                                                                    let uu____4312
                                                                    =
                                                                    let uu____4313
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4313
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4312,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4315
                                                                    =
                                                                    let uu____4327
                                                                    =
                                                                    let uu____4337
                                                                    =
                                                                    let uu____4338
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4338
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4337,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4340
                                                                    =
                                                                    let uu____4352
                                                                    =
                                                                    let uu____4364
                                                                    =
                                                                    let uu____4374
                                                                    =
                                                                    let uu____4375
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4375
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4374,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4377
                                                                    =
                                                                    let uu____4389
                                                                    =
                                                                    let uu____4401
                                                                    =
                                                                    let uu____4413
                                                                    =
                                                                    let uu____4425
                                                                    =
                                                                    let uu____4435
                                                                    =
                                                                    let uu____4436
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4436
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4435,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4438
                                                                    =
                                                                    let uu____4450
                                                                    =
                                                                    let uu____4460
                                                                    =
                                                                    let uu____4461
                                                                    =
                                                                    let uu____4469
                                                                    =
                                                                    let uu____4470
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4470
                                                                     in
                                                                    ((fun
                                                                    uu____4476
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4469)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4461
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4460,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4480
                                                                    =
                                                                    let uu____4492
                                                                    =
                                                                    let uu____4502
                                                                    =
                                                                    let uu____4503
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4503
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4502,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4505
                                                                    =
                                                                    let uu____4517
                                                                    =
                                                                    let uu____4529
                                                                    =
                                                                    let uu____4539
                                                                    =
                                                                    let uu____4540
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4540
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4539,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4542
                                                                    =
                                                                    let uu____4554
                                                                    =
                                                                    let uu____4566
                                                                    =
                                                                    let uu____4578
                                                                    =
                                                                    let uu____4590
                                                                    =
                                                                    let uu____4602
                                                                    =
                                                                    let uu____4612
                                                                    =
                                                                    let uu____4613
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4613
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4612,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4615
                                                                    =
                                                                    let uu____4627
                                                                    =
                                                                    let uu____4637
                                                                    =
                                                                    let uu____4638
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4638
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4637,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4640
                                                                    =
                                                                    let uu____4652
                                                                    =
                                                                    let uu____4664
                                                                    =
                                                                    let uu____4676
                                                                    =
                                                                    let uu____4686
                                                                    =
                                                                    let uu____4687
                                                                    =
                                                                    let uu____4695
                                                                    =
                                                                    let uu____4696
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4696
                                                                     in
                                                                    ((fun
                                                                    uu____4702
                                                                     ->
                                                                    (
                                                                    let uu____4704
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4704);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4695)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4687
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4686,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4676]
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4664
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4652
                                                                     in
                                                                    uu____4627
                                                                    ::
                                                                    uu____4640
                                                                     in
                                                                    uu____4602
                                                                    ::
                                                                    uu____4615
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4590
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4578
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4566
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4554
                                                                     in
                                                                    uu____4529
                                                                    ::
                                                                    uu____4542
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4517
                                                                     in
                                                                    uu____4492
                                                                    ::
                                                                    uu____4505
                                                                     in
                                                                    uu____4450
                                                                    ::
                                                                    uu____4480
                                                                     in
                                                                    uu____4425
                                                                    ::
                                                                    uu____4438
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4413
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4401
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4389
                                                                     in
                                                                    uu____4364
                                                                    ::
                                                                    uu____4377
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4352
                                                                     in
                                                                    uu____4327
                                                                    ::
                                                                    uu____4340
                                                                     in
                                                                    uu____4302
                                                                    ::
                                                                    uu____4315
                                                                     in
                                                                    uu____4277
                                                                    ::
                                                                    uu____4290
                                                                     in
                                                                    uu____4252
                                                                    ::
                                                                    uu____4265
                                                                     in
                                                                    uu____4227
                                                                    ::
                                                                    uu____4240
                                                                     in
                                                                    uu____4202
                                                                    ::
                                                                    uu____4215
                                                                     in
                                                                    uu____4177
                                                                    ::
                                                                    uu____4190
                                                                     in
                                                                    uu____4152
                                                                    ::
                                                                    uu____4165
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4140
                                                                     in
                                                                    uu____4115
                                                                    ::
                                                                    uu____4128
                                                                     in
                                                                    uu____4090
                                                                    ::
                                                                    uu____4103
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4078
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4066
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4054
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4042
                                                                     in
                                                                    uu____4017
                                                                    ::
                                                                    uu____4030
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____4005
                                                                     in
                                                                    uu____3980
                                                                    ::
                                                                    uu____3993
                                                                     in
                                                                    uu____3955
                                                                    ::
                                                                    uu____3968
                                                                     in
                                                                    uu____3930
                                                                    ::
                                                                    uu____3943
                                                                     in
                                                                    uu____3905
                                                                    ::
                                                                    uu____3918
                                                                     in
                                                                    uu____3880
                                                                    ::
                                                                    uu____3893
                                                                     in
                                                                    uu____3855
                                                                    ::
                                                                    uu____3868
                                                                     in
                                                                    uu____3830
                                                                    ::
                                                                    uu____3843
                                                                     in
                                                                    uu____3805
                                                                    ::
                                                                    uu____3818
                                                                     in
                                                                    uu____3780
                                                                    ::
                                                                    uu____3793
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3768
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3756
                                                                     in
                                                                    uu____3731
                                                                    ::
                                                                    uu____3744
                                                                     in
                                                                    uu____3706
                                                                    ::
                                                                    uu____3719
                                                                     in
                                                                    uu____3681
                                                                    ::
                                                                    uu____3694
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3669
                                                                     in
                                                                    uu____3644
                                                                    ::
                                                                    uu____3657
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3632
                                                                     in
                                                                    uu____3607
                                                                    ::
                                                                    uu____3620
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3595
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3583
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3571
                                                                     in
                                                                    uu____3546
                                                                    ::
                                                                    uu____3559
                                                                     in
                                                                    uu____3521
                                                                    ::
                                                                    uu____3534
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3509
                                                                     in
                                                                  uu____3484
                                                                    ::
                                                                    uu____3497
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "integer_overloading",
                                                                  BoolStr,
                                                                  "Type integer and machine integer constants using FStar.Integers, in support of overloading integer operations")
                                                                  ::
                                                                  uu____3472
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_ifuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                :: uu____3460
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "initial_fuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of recursive functions to try initially (default 2)")
                                                              :: uu____3448
                                                             in
                                                          uu____3423 ::
                                                            uu____3436
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "include",
                                                          (ReverseAccumulated
                                                             (PathStr "path")),
                                                          "A directory in which to search for files included on the command line")
                                                          :: uu____3411
                                                         in
                                                      uu____3386 ::
                                                        uu____3399
                                                       in
                                                    uu____3361 :: uu____3374
                                                     in
                                                  uu____3336 :: uu____3349
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "hint_file",
                                                  (PathStr "path"),
                                                  "Read/write hints to <path> (instead of module-specific hints files)")
                                                  :: uu____3324
                                                 in
                                              uu____3299 :: uu____3312  in
                                            uu____3274 :: uu____3287  in
                                          (FStar_Getopt.noshort,
                                            "extract_namespace",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr
                                                       "namespace name")))),
                                            "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                            :: uu____3262
                                           in
                                        (FStar_Getopt.noshort,
                                          "extract_module",
                                          (Accumulated
                                             (PostProcessed
                                                (pp_lowercase,
                                                  (SimpleStr "module_name")))),
                                          "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                          :: uu____3250
                                         in
                                      (FStar_Getopt.noshort, "extract",
                                        (Accumulated
                                           (SimpleStr
                                              "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                        "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                        :: uu____3238
                                       in
                                    uu____3213 :: uu____3226  in
                                  uu____3188 :: uu____3201  in
                                (FStar_Getopt.noshort, "dump_module",
                                  (Accumulated (SimpleStr "module_name")),
                                  "") :: uu____3176
                                 in
                              uu____3151 :: uu____3164  in
                            uu____3126 :: uu____3139  in
                          uu____3101 :: uu____3114  in
                        (FStar_Getopt.noshort, "dep",
                          (EnumStr ["make"; "graph"; "full"]),
                          "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                          :: uu____3089
                         in
                      (FStar_Getopt.noshort, "defensive",
                        (EnumStr ["no"; "warn"; "fail"]),
                        "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                        :: uu____3077
                       in
                    (FStar_Getopt.noshort, "debug_level",
                      (Accumulated
                         (OpenEnumStr
                            (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                      "Control the verbosity of debugging info") ::
                      uu____3065
                     in
                  (FStar_Getopt.noshort, "debug",
                    (Accumulated (SimpleStr "module_name")),
                    "Print lots of debugging information while checking module")
                    :: uu____3053
                   in
                (FStar_Getopt.noshort, "codegen-lib",
                  (Accumulated (SimpleStr "namespace")),
                  "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                  :: uu____3041
                 in
              (FStar_Getopt.noshort, "codegen",
                (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                "Generate code for further compilation to executable code, or build a compiler plugin")
                :: uu____3029
               in
            uu____3004 :: uu____3017  in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2992
           in
        uu____2967 :: uu____2980  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2955
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2943

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5615  ->
    let uu____5618 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5645  ->
         match uu____5645 with
         | (short,long,typ,doc) ->
             let uu____5661 =
               let uu____5673 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5673, doc)  in
             mk_spec uu____5661) uu____5618

let (settable : Prims.string -> Prims.bool) =
  fun uu___79_5683  ->
    match uu___79_5683 with
    | "admit_smt_queries" -> true
    | "admit_except" -> true
    | "debug" -> true
    | "debug_level" -> true
    | "defensive" -> true
    | "detail_errors" -> true
    | "detail_hint_replay" -> true
    | "eager_inference" -> true
    | "eager_subtyping" -> true
    | "hide_uvar_nums" -> true
    | "hint_info" -> true
    | "hint_file" -> true
    | "initial_fuel" -> true
    | "initial_ifuel" -> true
    | "integer_overloading" -> true
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
    | uu____5684 -> false
  
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
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5758  ->
          match uu____5758 with
          | (uu____5770,x,uu____5772,uu____5773) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5835  ->
          match uu____5835 with
          | (uu____5847,x,uu____5849,uu____5850) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5861  ->
    let uu____5862 = specs ()  in display_usage_aux uu____5862
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5886 -> true
    | uu____5887 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5894 -> uu____5894
  
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
          let uu____5922 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5922
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5950  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5955 =
             let uu____5958 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5958 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5955)
       in
    let uu____6015 =
      let uu____6018 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6018
       in
    (res, uu____6015)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6056  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6095 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6095 (fun x  -> ())  in
     (let uu____6101 =
        let uu____6106 =
          let uu____6107 = FStar_List.map mk_string old_verify_module  in
          List uu____6107  in
        ("verify_module", uu____6106)  in
      set_option' uu____6101);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6117 =
        let uu____6118 =
          let uu____6119 =
            let uu____6120 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6120  in
          (FStar_String.length f1) - uu____6119  in
        uu____6118 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6117  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6126 = get_lax ()  in
    if uu____6126
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6136 = module_name_of_file_name fn  in should_verify uu____6136
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6142 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6142
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6150 = should_verify m  in
    if uu____6150 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6158  ->
    let uu____6159 = get_no_default_includes ()  in
    if uu____6159
    then get_include ()
    else
      (let lib_paths =
         let uu____6166 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6166 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6175 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6175
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6189 =
         let uu____6192 = get_include ()  in
         FStar_List.append uu____6192 ["."]  in
       FStar_List.append lib_paths uu____6189)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____6205 = FStar_Util.smap_try_find file_map filename  in
    match uu____6205 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            let uu____6221 = FStar_Util.is_path_absolute filename  in
            if uu____6221
            then
              (if FStar_Util.file_exists filename
               then FStar_Pervasives_Native.Some filename
               else FStar_Pervasives_Native.None)
            else
              (let uu____6228 =
                 let uu____6231 = include_path ()  in
                 FStar_List.rev uu____6231  in
               FStar_Util.find_map uu____6228
                 (fun p  ->
                    let path =
                      if p = "."
                      then filename
                      else FStar_Util.join_paths p filename  in
                    if FStar_Util.file_exists path
                    then FStar_Pervasives_Native.Some path
                    else FStar_Pervasives_Native.None))
          with | uu____6247 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____6256  ->
    let uu____6257 = get_prims ()  in
    match uu____6257 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6261 = find_file filename  in
        (match uu____6261 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6265 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6265)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6271  ->
    let uu____6272 = prims ()  in FStar_Util.basename uu____6272
  
let (pervasives : unit -> Prims.string) =
  fun uu____6277  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____6279 = find_file filename  in
    match uu____6279 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____6283 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6283
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6288  ->
    let uu____6289 = pervasives ()  in FStar_Util.basename uu____6289
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6294  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____6296 = find_file filename  in
    match uu____6296 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____6300 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6300
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____6306 = get_odir ()  in
    match uu____6306 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____6315 = get_cache_dir ()  in
    match uu____6315 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6319 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____6319
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
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
             let uu____6385 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____6385  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____6393 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6393 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6463 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6463 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6472  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6477  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6484  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6489  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____6494  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6500 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6506 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6512 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6518 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6525  ->
    let uu____6526 = get_codegen ()  in
    FStar_Util.map_opt uu____6526
      (fun uu___80_6530  ->
         match uu___80_6530 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6531 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6540  ->
    let uu____6541 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6541
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6558  -> let uu____6559 = get_debug ()  in uu____6559 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6569 = get_debug ()  in
    FStar_All.pipe_right uu____6569 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6586 = get_debug ()  in
       FStar_All.pipe_right uu____6586 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6595  -> let uu____6596 = get_defensive ()  in uu____6596 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6601  ->
    let uu____6602 = get_defensive ()  in uu____6602 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6609  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6614  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6619  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6624  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6630 = get_dump_module ()  in
    FStar_All.pipe_right uu____6630 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6639  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6644  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6650 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6650
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6684  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6689  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6694  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6701  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6706  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6711  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6716  ->
    let uu____6717 = get_initial_fuel ()  in
    let uu____6718 = get_max_fuel ()  in Prims.min uu____6717 uu____6718
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6723  ->
    let uu____6724 = get_initial_ifuel ()  in
    let uu____6725 = get_max_ifuel ()  in Prims.min uu____6724 uu____6725
  
let (interactive : unit -> Prims.bool) =
  fun uu____6730  -> (get_in ()) || (get_ide ()) 
let (integer_overloading : unit -> Prims.bool) =
  fun uu____6735  -> get_integer_overloading () 
let (lax : unit -> Prims.bool) = fun uu____6740  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6747  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6752  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6757  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6762  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6767  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6772  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6777  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6782  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6787  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6792  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6797  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6804 = get_no_extract ()  in
    FStar_All.pipe_right uu____6804
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6815  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6820  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6825  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6832  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6837  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6842  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6847  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6852  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6857  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6862  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6867  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____6872  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____6877  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6884  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____6889  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6894  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6899  ->
    let uu____6900 = get_smtencoding_nl_arith_repr ()  in
    uu____6900 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6905  ->
    let uu____6906 = get_smtencoding_nl_arith_repr ()  in
    uu____6906 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6911  ->
    let uu____6912 = get_smtencoding_nl_arith_repr ()  in
    uu____6912 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6917  ->
    let uu____6918 = get_smtencoding_l_arith_repr ()  in
    uu____6918 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6923  ->
    let uu____6924 = get_smtencoding_l_arith_repr ()  in
    uu____6924 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6929  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6934  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6939  -> get_tactic_trace_d () 
let (timing : unit -> Prims.bool) = fun uu____6944  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____6949  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____6954  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____6959  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____6964  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____6969  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____6974  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6981  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____6986  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____6999  ->
    let uu____7000 = get_using_facts_from ()  in
    match uu____7000 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7038  ->
    let uu____7039 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____7039
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7046  ->
    let uu____7047 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____7047 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7050 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7057  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____7062  ->
    let uu____7063 = get_smt ()  in
    match uu____7063 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7073  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____7078  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____7083  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7088  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____7093  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7098  ->
    (get_use_two_phase_tc ()) &&
      (let uu____7100 = lax ()  in Prims.op_Negation uu____7100)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7105  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7110  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7115  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7120  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7127 = get_extract ()  in
    match uu____7127 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7138 =
            let uu____7151 = get_no_extract ()  in
            let uu____7154 = get_extract_namespace ()  in
            let uu____7157 = get_extract_module ()  in
            (uu____7151, uu____7154, uu____7157)  in
          match uu____7138 with
          | ([],[],[]) -> ()
          | uu____7172 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7220,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7239 -> false  in
          let uu____7248 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7282  ->
                    match uu____7282 with
                    | (path,uu____7290) -> matches_path m_components path))
             in
          match uu____7248 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____7301,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____7321 = get_extract_namespace ()  in
          match uu____7321 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____7337 = get_extract_module ()  in
          match uu____7337 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____7349 = no_extract m1  in Prims.op_Negation uu____7349) &&
          (let uu____7351 =
             let uu____7360 = get_extract_namespace ()  in
             let uu____7363 = get_extract_module ()  in
             (uu____7360, uu____7363)  in
           (match uu____7351 with
            | ([],[]) -> true
            | uu____7374 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  