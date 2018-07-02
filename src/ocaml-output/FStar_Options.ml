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
  fun uu____236  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____260  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___75_284  ->
    match uu___75_284 with
    | Bool b -> b
    | uu____286 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___76_291  ->
    match uu___76_291 with
    | Int b -> b
    | uu____293 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___77_298  ->
    match uu___77_298 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____301 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___78_308  ->
    match uu___78_308 with
    | List ts -> ts
    | uu____314 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____323 .
    (option_val -> 'Auu____323) -> option_val -> 'Auu____323 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____341 = as_list' x  in
      FStar_All.pipe_right uu____341 (FStar_List.map as_t)
  
let as_option :
  'Auu____354 .
    (option_val -> 'Auu____354) ->
      option_val -> 'Auu____354 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___79_369  ->
      match uu___79_369 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____373 = as_t v1  in FStar_Pervasives_Native.Some uu____373
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___80_380  ->
    match uu___80_380 with
    | List ls ->
        let uu____386 =
          FStar_List.map
            (fun l  ->
               let uu____396 = as_string l  in FStar_Util.split uu____396 ",")
            ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____386
    | uu____403 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let (fstar_options : optionstate Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : unit -> optionstate) =
  fun uu____429  ->
    let uu____430 = FStar_ST.op_Bang fstar_options  in
    FStar_List.hd uu____430
  
let (pop : unit -> unit) =
  fun uu____460  ->
    let uu____461 = FStar_ST.op_Bang fstar_options  in
    match uu____461 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____487::[] -> failwith "TOO MANY POPS!"
    | uu____488::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____519  ->
    let uu____520 =
      let uu____523 =
        let uu____524 = peek ()  in FStar_Util.smap_copy uu____524  in
      let uu____527 = FStar_ST.op_Bang fstar_options  in uu____523 ::
        uu____527
       in
    FStar_ST.op_Colon_Equals fstar_options uu____520
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____581 = FStar_ST.op_Bang fstar_options  in
    match uu____581 with
    | [] -> failwith "set on empty option stack"
    | uu____607::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
  
let (snapshot : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____642  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  -> let uu____662 = peek ()  in FStar_Util.smap_add uu____662 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____673  -> match uu____673 with | (k,v1) -> set_option k v1 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f ()  in pop (); retv) 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____720 =
      let uu____723 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____723
       in
    FStar_ST.op_Colon_Equals light_off_files uu____720
  
let (defaults :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 Prims.list) =
  [("__temp_no_proj", (List []));
  ("__temp_fast_implicits", (Bool false));
  ("abort_on", (Int (Prims.parse_int "0")));
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
  ("__tactics_nbe", (Bool false));
  ("warn_error", (String ""));
  ("use_extracted_interfaces", (Bool false))] 
let (init : unit -> unit) =
  fun uu____1174  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1191  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1248 =
      let uu____1251 = peek ()  in FStar_Util.smap_try_find uu____1251 s  in
    match uu____1248 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1261 . Prims.string -> (option_val -> 'Auu____1261) -> 'Auu____1261
  = fun s  -> fun c  -> let uu____1277 = get_option s  in c uu____1277 
let (get_abort_on : unit -> Prims.int) =
  fun uu____1282  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1287  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1294  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1301  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1308  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1315  -> lookup_opt "cache_off" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1322  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1331  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1340  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1349  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____1356  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1363  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1370  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1375  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1380  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1387  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1394  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1399  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1408  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1421  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1430  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1437  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1442  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1447  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1454  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1461  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1466  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1473  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1480  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1485  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1490  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1495  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1502  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1509  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1514  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1519  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1524  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1529  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1534  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1539  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1544  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1551  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1558  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1563  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1568  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1575  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1582  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1589  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1596  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1601  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1606  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1611  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1616  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1621  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1626  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1631  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1636  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1643  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1650  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1657  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1664  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1669  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1674  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1679  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1684  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1689  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____1694  -> lookup_opt "__tactics_nbe" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____1699  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1704  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1709  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1714  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1719  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1724  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1729  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1736  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1743  ->
    let uu____1744 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1744
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1753  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1766  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1775  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1784  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1791  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1796  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1803  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1810  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1815  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1820  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1825  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1830  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1835  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1840  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1845  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1850  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___81_1855  ->
    match uu___81_1855 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1867 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1873 = get_debug_level ()  in
    FStar_All.pipe_right uu____1873
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2006  ->
    let uu____2007 =
      let uu____2008 = FStar_ST.op_Bang _version  in
      let uu____2028 = FStar_ST.op_Bang _platform  in
      let uu____2048 = FStar_ST.op_Bang _compiler  in
      let uu____2068 = FStar_ST.op_Bang _date  in
      let uu____2088 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2008
        uu____2028 uu____2048 uu____2068 uu____2088
       in
    FStar_Util.print_string uu____2007
  
let display_usage_aux :
  'Auu____2114 'Auu____2115 .
    ('Auu____2114,Prims.string,'Auu____2115 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2163  ->
         match uu____2163 with
         | (uu____2174,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2186 =
                      let uu____2187 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2187  in
                    FStar_Util.print_string uu____2186
                  else
                    (let uu____2189 =
                       let uu____2190 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2190 doc  in
                     FStar_Util.print_string uu____2189)
              | FStar_Getopt.OneArg (uu____2191,argname) ->
                  if doc = ""
                  then
                    let uu____2199 =
                      let uu____2200 = FStar_Util.colorize_bold flag  in
                      let uu____2201 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2200 uu____2201
                       in
                    FStar_Util.print_string uu____2199
                  else
                    (let uu____2203 =
                       let uu____2204 = FStar_Util.colorize_bold flag  in
                       let uu____2205 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2204
                         uu____2205 doc
                        in
                     FStar_Util.print_string uu____2203))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2233 = o  in
    match uu____2233 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2269 =
                let uu____2270 = f ()  in set_option name uu____2270  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2285 = f x  in set_option name uu____2285
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2305 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2305  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2328 =
        let uu____2331 = lookup_opt name as_list'  in
        FStar_List.append uu____2331 [value]  in
      mk_list uu____2328
  
let accumulate_string :
  'Auu____2344 .
    Prims.string -> ('Auu____2344 -> Prims.string) -> 'Auu____2344 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2365 =
          let uu____2366 =
            let uu____2367 = post_processor value  in mk_string uu____2367
             in
          accumulated_option name uu____2366  in
        set_option name uu____2365
  
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
    match projectee with | Const _0 -> true | uu____2463 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2477 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2490 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2497 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2511 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2527 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2553 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2592 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2627 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2641 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2662 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2700 -> true
    | uu____2701 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2708 -> uu____2708
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___86_2726  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____2728 ->
                      let uu____2729 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____2729 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____2733 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____2733
                  | PathStr uu____2736 -> mk_path str_val
                  | SimpleStr uu____2737 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____2742 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____2757 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____2757
                  | Accumulated elem_spec ->
                      let v1 = parse_opt_val opt_name elem_spec str_val  in
                      accumulated_option opt_name v1
                  | ReverseAccumulated elem_spec ->
                      let v1 = parse_opt_val opt_name elem_spec str_val  in
                      reverse_accumulated_option opt_name v1
                  | WithSideEffect (side_effect,elem_spec) ->
                      (side_effect ();
                       parse_opt_val opt_name elem_spec str_val))) ()
        with
        | InvalidArgument opt_name1 ->
            let uu____2776 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2776
  
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
    | PostProcessed (uu____2813,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2823,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2850 = desc_of_opt_type typ  in
      match uu____2850 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2856  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2873 =
      let uu____2874 = as_string s  in FStar_String.lowercase uu____2874  in
    mk_string uu____2873
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2922  ->
    let uu____2934 =
      let uu____2946 =
        let uu____2958 =
          let uu____2970 =
            let uu____2980 =
              let uu____2981 = mk_bool true  in Const uu____2981  in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____2980,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
             in
          let uu____2983 =
            let uu____2995 =
              let uu____3007 =
                let uu____3017 =
                  let uu____3018 = mk_bool true  in Const uu____3018  in
                (FStar_Getopt.noshort, "cache_off", uu____3017,
                  "Do not read or write any .checked files")
                 in
              let uu____3020 =
                let uu____3032 =
                  let uu____3044 =
                    let uu____3056 =
                      let uu____3068 =
                        let uu____3080 =
                          let uu____3092 =
                            let uu____3104 =
                              let uu____3114 =
                                let uu____3115 = mk_bool true  in
                                Const uu____3115  in
                              (FStar_Getopt.noshort, "detail_errors",
                                uu____3114,
                                "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                               in
                            let uu____3117 =
                              let uu____3129 =
                                let uu____3139 =
                                  let uu____3140 = mk_bool true  in
                                  Const uu____3140  in
                                (FStar_Getopt.noshort, "detail_hint_replay",
                                  uu____3139,
                                  "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                 in
                              let uu____3142 =
                                let uu____3154 =
                                  let uu____3164 =
                                    let uu____3165 = mk_bool true  in
                                    Const uu____3165  in
                                  (FStar_Getopt.noshort, "doc", uu____3164,
                                    "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                   in
                                let uu____3167 =
                                  let uu____3179 =
                                    let uu____3191 =
                                      let uu____3201 =
                                        let uu____3202 = mk_bool true  in
                                        Const uu____3202  in
                                      (FStar_Getopt.noshort,
                                        "eager_inference", uu____3201,
                                        "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                       in
                                    let uu____3204 =
                                      let uu____3216 =
                                        let uu____3226 =
                                          let uu____3227 = mk_bool true  in
                                          Const uu____3227  in
                                        (FStar_Getopt.noshort,
                                          "eager_subtyping", uu____3226,
                                          "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                         in
                                      let uu____3229 =
                                        let uu____3241 =
                                          let uu____3253 =
                                            let uu____3265 =
                                              let uu____3277 =
                                                let uu____3287 =
                                                  let uu____3288 =
                                                    mk_bool true  in
                                                  Const uu____3288  in
                                                (FStar_Getopt.noshort,
                                                  "expose_interfaces",
                                                  uu____3287,
                                                  "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                 in
                                              let uu____3290 =
                                                let uu____3302 =
                                                  let uu____3312 =
                                                    let uu____3313 =
                                                      mk_bool true  in
                                                    Const uu____3313  in
                                                  (FStar_Getopt.noshort,
                                                    "hide_uvar_nums",
                                                    uu____3312,
                                                    "Don't print unification variable numbers")
                                                   in
                                                let uu____3315 =
                                                  let uu____3327 =
                                                    let uu____3339 =
                                                      let uu____3349 =
                                                        let uu____3350 =
                                                          mk_bool true  in
                                                        Const uu____3350  in
                                                      (FStar_Getopt.noshort,
                                                        "hint_info",
                                                        uu____3349,
                                                        "Print information regarding hints (deprecated; use --query_stats instead)")
                                                       in
                                                    let uu____3352 =
                                                      let uu____3364 =
                                                        let uu____3374 =
                                                          let uu____3375 =
                                                            mk_bool true  in
                                                          Const uu____3375
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "in", uu____3374,
                                                          "Legacy interactive mode; reads input from stdin")
                                                         in
                                                      let uu____3377 =
                                                        let uu____3389 =
                                                          let uu____3399 =
                                                            let uu____3400 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3400
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "ide",
                                                            uu____3399,
                                                            "JSON-based interactive mode for IDEs")
                                                           in
                                                        let uu____3402 =
                                                          let uu____3414 =
                                                            let uu____3426 =
                                                              let uu____3436
                                                                =
                                                                let uu____3437
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____3437
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "indent",
                                                                uu____3436,
                                                                "Parses and outputs the files on the command line")
                                                               in
                                                            let uu____3439 =
                                                              let uu____3451
                                                                =
                                                                let uu____3463
                                                                  =
                                                                  let uu____3475
                                                                    =
                                                                    let uu____3485
                                                                    =
                                                                    let uu____3486
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3486
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3485,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                  let uu____3488
                                                                    =
                                                                    let uu____3500
                                                                    =
                                                                    let uu____3512
                                                                    =
                                                                    let uu____3522
                                                                    =
                                                                    let uu____3523
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3523
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3522,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3525
                                                                    =
                                                                    let uu____3537
                                                                    =
                                                                    let uu____3547
                                                                    =
                                                                    let uu____3548
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3548
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3547,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3550
                                                                    =
                                                                    let uu____3562
                                                                    =
                                                                    let uu____3574
                                                                    =
                                                                    let uu____3586
                                                                    =
                                                                    let uu____3598
                                                                    =
                                                                    let uu____3608
                                                                    =
                                                                    let uu____3609
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3609
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3608,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3611
                                                                    =
                                                                    let uu____3623
                                                                    =
                                                                    let uu____3635
                                                                    =
                                                                    let uu____3645
                                                                    =
                                                                    let uu____3646
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3646
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3645,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3648
                                                                    =
                                                                    let uu____3660
                                                                    =
                                                                    let uu____3672
                                                                    =
                                                                    let uu____3682
                                                                    =
                                                                    let uu____3683
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3683
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3682,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3685
                                                                    =
                                                                    let uu____3697
                                                                    =
                                                                    let uu____3707
                                                                    =
                                                                    let uu____3708
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3708
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3707,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3710
                                                                    =
                                                                    let uu____3722
                                                                    =
                                                                    let uu____3732
                                                                    =
                                                                    let uu____3733
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3733
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3732,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3735
                                                                    =
                                                                    let uu____3747
                                                                    =
                                                                    let uu____3759
                                                                    =
                                                                    let uu____3771
                                                                    =
                                                                    let uu____3781
                                                                    =
                                                                    let uu____3782
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3782
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3781,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3784
                                                                    =
                                                                    let uu____3796
                                                                    =
                                                                    let uu____3806
                                                                    =
                                                                    let uu____3807
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3807
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3806,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3809
                                                                    =
                                                                    let uu____3821
                                                                    =
                                                                    let uu____3831
                                                                    =
                                                                    let uu____3832
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3832
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3831,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3834
                                                                    =
                                                                    let uu____3846
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
                                                                    "print_implicits",
                                                                    uu____3856,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3859
                                                                    =
                                                                    let uu____3871
                                                                    =
                                                                    let uu____3881
                                                                    =
                                                                    let uu____3882
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3882
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3881,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3884
                                                                    =
                                                                    let uu____3896
                                                                    =
                                                                    let uu____3906
                                                                    =
                                                                    let uu____3907
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3907
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3906,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3909
                                                                    =
                                                                    let uu____3921
                                                                    =
                                                                    let uu____3931
                                                                    =
                                                                    let uu____3932
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3932
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3931,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3934
                                                                    =
                                                                    let uu____3946
                                                                    =
                                                                    let uu____3956
                                                                    =
                                                                    let uu____3957
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3957
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3956,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3959
                                                                    =
                                                                    let uu____3971
                                                                    =
                                                                    let uu____3981
                                                                    =
                                                                    let uu____3982
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3982
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3981,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3984
                                                                    =
                                                                    let uu____3996
                                                                    =
                                                                    let uu____4008
                                                                    =
                                                                    let uu____4018
                                                                    =
                                                                    let uu____4019
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4019
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4018,
                                                                    " ")  in
                                                                    let uu____4021
                                                                    =
                                                                    let uu____4033
                                                                    =
                                                                    let uu____4045
                                                                    =
                                                                    let uu____4057
                                                                    =
                                                                    let uu____4069
                                                                    =
                                                                    let uu____4081
                                                                    =
                                                                    let uu____4091
                                                                    =
                                                                    let uu____4092
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4092
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4091,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4094
                                                                    =
                                                                    let uu____4106
                                                                    =
                                                                    let uu____4116
                                                                    =
                                                                    let uu____4117
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4117
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4116,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4119
                                                                    =
                                                                    let uu____4131
                                                                    =
                                                                    let uu____4143
                                                                    =
                                                                    let uu____4153
                                                                    =
                                                                    let uu____4154
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4154
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____4153,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____4156
                                                                    =
                                                                    let uu____4168
                                                                    =
                                                                    let uu____4178
                                                                    =
                                                                    let uu____4179
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4179
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4178,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4181
                                                                    =
                                                                    let uu____4193
                                                                    =
                                                                    let uu____4203
                                                                    =
                                                                    let uu____4204
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4204
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4203,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4206
                                                                    =
                                                                    let uu____4218
                                                                    =
                                                                    let uu____4228
                                                                    =
                                                                    let uu____4229
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4229
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4228,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4231
                                                                    =
                                                                    let uu____4243
                                                                    =
                                                                    let uu____4253
                                                                    =
                                                                    let uu____4254
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4254
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4253,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4256
                                                                    =
                                                                    let uu____4268
                                                                    =
                                                                    let uu____4278
                                                                    =
                                                                    let uu____4279
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4279
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4278,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4281
                                                                    =
                                                                    let uu____4293
                                                                    =
                                                                    let uu____4303
                                                                    =
                                                                    let uu____4304
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4304
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4303,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4306
                                                                    =
                                                                    let uu____4318
                                                                    =
                                                                    let uu____4328
                                                                    =
                                                                    let uu____4329
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4329
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4328,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4331
                                                                    =
                                                                    let uu____4343
                                                                    =
                                                                    let uu____4353
                                                                    =
                                                                    let uu____4354
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4354
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4353,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4356
                                                                    =
                                                                    let uu____4368
                                                                    =
                                                                    let uu____4380
                                                                    =
                                                                    let uu____4390
                                                                    =
                                                                    let uu____4391
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4391
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4390,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4393
                                                                    =
                                                                    let uu____4405
                                                                    =
                                                                    let uu____4417
                                                                    =
                                                                    let uu____4429
                                                                    =
                                                                    let uu____4441
                                                                    =
                                                                    let uu____4451
                                                                    =
                                                                    let uu____4452
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4452
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4451,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4454
                                                                    =
                                                                    let uu____4466
                                                                    =
                                                                    let uu____4476
                                                                    =
                                                                    let uu____4477
                                                                    =
                                                                    let uu____4485
                                                                    =
                                                                    let uu____4486
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4486
                                                                     in
                                                                    ((fun
                                                                    uu____4492
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4485)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4477
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4476,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4496
                                                                    =
                                                                    let uu____4508
                                                                    =
                                                                    let uu____4518
                                                                    =
                                                                    let uu____4519
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4519
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4518,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4521
                                                                    =
                                                                    let uu____4533
                                                                    =
                                                                    let uu____4545
                                                                    =
                                                                    let uu____4555
                                                                    =
                                                                    let uu____4556
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4556
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4555,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4558
                                                                    =
                                                                    let uu____4570
                                                                    =
                                                                    let uu____4582
                                                                    =
                                                                    let uu____4594
                                                                    =
                                                                    let uu____4606
                                                                    =
                                                                    let uu____4618
                                                                    =
                                                                    let uu____4628
                                                                    =
                                                                    let uu____4629
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4629
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4628,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4631
                                                                    =
                                                                    let uu____4643
                                                                    =
                                                                    let uu____4653
                                                                    =
                                                                    let uu____4654
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4654
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4653,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4656
                                                                    =
                                                                    let uu____4668
                                                                    =
                                                                    let uu____4680
                                                                    =
                                                                    let uu____4692
                                                                    =
                                                                    let uu____4702
                                                                    =
                                                                    let uu____4703
                                                                    =
                                                                    let uu____4711
                                                                    =
                                                                    let uu____4712
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4712
                                                                     in
                                                                    ((fun
                                                                    uu____4718
                                                                     ->
                                                                    (
                                                                    let uu____4720
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4720);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4711)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4703
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4702,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4692]
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4680
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4668
                                                                     in
                                                                    uu____4643
                                                                    ::
                                                                    uu____4656
                                                                     in
                                                                    uu____4618
                                                                    ::
                                                                    uu____4631
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4606
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4594
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4582
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4570
                                                                     in
                                                                    uu____4545
                                                                    ::
                                                                    uu____4558
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4533
                                                                     in
                                                                    uu____4508
                                                                    ::
                                                                    uu____4521
                                                                     in
                                                                    uu____4466
                                                                    ::
                                                                    uu____4496
                                                                     in
                                                                    uu____4441
                                                                    ::
                                                                    uu____4454
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4429
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4417
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4405
                                                                     in
                                                                    uu____4380
                                                                    ::
                                                                    uu____4393
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4368
                                                                     in
                                                                    uu____4343
                                                                    ::
                                                                    uu____4356
                                                                     in
                                                                    uu____4318
                                                                    ::
                                                                    uu____4331
                                                                     in
                                                                    uu____4293
                                                                    ::
                                                                    uu____4306
                                                                     in
                                                                    uu____4268
                                                                    ::
                                                                    uu____4281
                                                                     in
                                                                    uu____4243
                                                                    ::
                                                                    uu____4256
                                                                     in
                                                                    uu____4218
                                                                    ::
                                                                    uu____4231
                                                                     in
                                                                    uu____4193
                                                                    ::
                                                                    uu____4206
                                                                     in
                                                                    uu____4168
                                                                    ::
                                                                    uu____4181
                                                                     in
                                                                    uu____4143
                                                                    ::
                                                                    uu____4156
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4131
                                                                     in
                                                                    uu____4106
                                                                    ::
                                                                    uu____4119
                                                                     in
                                                                    uu____4081
                                                                    ::
                                                                    uu____4094
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4069
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4057
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4045
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4033
                                                                     in
                                                                    uu____4008
                                                                    ::
                                                                    uu____4021
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3996
                                                                     in
                                                                    uu____3971
                                                                    ::
                                                                    uu____3984
                                                                     in
                                                                    uu____3946
                                                                    ::
                                                                    uu____3959
                                                                     in
                                                                    uu____3921
                                                                    ::
                                                                    uu____3934
                                                                     in
                                                                    uu____3896
                                                                    ::
                                                                    uu____3909
                                                                     in
                                                                    uu____3871
                                                                    ::
                                                                    uu____3884
                                                                     in
                                                                    uu____3846
                                                                    ::
                                                                    uu____3859
                                                                     in
                                                                    uu____3821
                                                                    ::
                                                                    uu____3834
                                                                     in
                                                                    uu____3796
                                                                    ::
                                                                    uu____3809
                                                                     in
                                                                    uu____3771
                                                                    ::
                                                                    uu____3784
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3759
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3747
                                                                     in
                                                                    uu____3722
                                                                    ::
                                                                    uu____3735
                                                                     in
                                                                    uu____3697
                                                                    ::
                                                                    uu____3710
                                                                     in
                                                                    uu____3672
                                                                    ::
                                                                    uu____3685
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3660
                                                                     in
                                                                    uu____3635
                                                                    ::
                                                                    uu____3648
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3623
                                                                     in
                                                                    uu____3598
                                                                    ::
                                                                    uu____3611
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3586
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3574
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3562
                                                                     in
                                                                    uu____3537
                                                                    ::
                                                                    uu____3550
                                                                     in
                                                                    uu____3512
                                                                    ::
                                                                    uu____3525
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3500
                                                                     in
                                                                  uu____3475
                                                                    ::
                                                                    uu____3488
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_ifuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                  ::
                                                                  uu____3463
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_fuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of recursive functions to try initially (default 2)")
                                                                :: uu____3451
                                                               in
                                                            uu____3426 ::
                                                              uu____3439
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "include",
                                                            (ReverseAccumulated
                                                               (PathStr
                                                                  "path")),
                                                            "A directory in which to search for files included on the command line")
                                                            :: uu____3414
                                                           in
                                                        uu____3389 ::
                                                          uu____3402
                                                         in
                                                      uu____3364 ::
                                                        uu____3377
                                                       in
                                                    uu____3339 :: uu____3352
                                                     in
                                                  (FStar_Getopt.noshort,
                                                    "hint_file",
                                                    (PathStr "path"),
                                                    "Read/write hints to <path> (instead of module-specific hints files)")
                                                    :: uu____3327
                                                   in
                                                uu____3302 :: uu____3315  in
                                              uu____3277 :: uu____3290  in
                                            (FStar_Getopt.noshort,
                                              "extract_namespace",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "namespace name")))),
                                              "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                              :: uu____3265
                                             in
                                          (FStar_Getopt.noshort,
                                            "extract_module",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr "module_name")))),
                                            "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                            :: uu____3253
                                           in
                                        (FStar_Getopt.noshort, "extract",
                                          (Accumulated
                                             (SimpleStr
                                                "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                          "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                          :: uu____3241
                                         in
                                      uu____3216 :: uu____3229  in
                                    uu____3191 :: uu____3204  in
                                  (FStar_Getopt.noshort, "dump_module",
                                    (Accumulated (SimpleStr "module_name")),
                                    "") :: uu____3179
                                   in
                                uu____3154 :: uu____3167  in
                              uu____3129 :: uu____3142  in
                            uu____3104 :: uu____3117  in
                          (FStar_Getopt.noshort, "dep",
                            (EnumStr ["make"; "graph"; "full"]),
                            "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                            :: uu____3092
                           in
                        (FStar_Getopt.noshort, "defensive",
                          (EnumStr ["no"; "warn"; "fail"]),
                          "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                          :: uu____3080
                         in
                      (FStar_Getopt.noshort, "debug_level",
                        (Accumulated
                           (OpenEnumStr
                              (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                        "Control the verbosity of debugging info") ::
                        uu____3068
                       in
                    (FStar_Getopt.noshort, "debug",
                      (Accumulated (SimpleStr "module_name")),
                      "Print lots of debugging information while checking module")
                      :: uu____3056
                     in
                  (FStar_Getopt.noshort, "codegen-lib",
                    (Accumulated (SimpleStr "namespace")),
                    "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                    :: uu____3044
                   in
                (FStar_Getopt.noshort, "codegen",
                  (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                  "Generate code for further compilation to executable code, or build a compiler plugin")
                  :: uu____3032
                 in
              uu____3007 :: uu____3020  in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____2995
             in
          uu____2970 :: uu____2983  in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____2958
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____2946
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___82_5646  ->
             match uu___82_5646 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____2934

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5669  ->
    let uu____5672 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5699  ->
         match uu____5699 with
         | (short,long,typ,doc) ->
             let uu____5715 =
               let uu____5727 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5727, doc)  in
             mk_spec uu____5715) uu____5672

let (settable : Prims.string -> Prims.bool) =
  fun uu___83_5737  ->
    match uu___83_5737 with
    | "abort_on" -> true
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
    | "__tactics_nbe" -> true
    | "__temp_fast_implicits" -> true
    | "__temp_no_proj" -> true
    | "reuse_hint_for" -> true
    | "warn_error" -> true
    | "z3rlimit_factor" -> true
    | "z3rlimit" -> true
    | "z3refresh" -> true
    | "use_two_phase_tc" -> true
    | "vcgen.optimize_bind_as_seq" -> true
    | uu____5738 -> false
  
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
       (fun uu____5812  ->
          match uu____5812 with
          | (uu____5824,x,uu____5826,uu____5827) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5889  ->
          match uu____5889 with
          | (uu____5901,x,uu____5903,uu____5904) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5915  ->
    let uu____5916 = specs ()  in display_usage_aux uu____5916
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5940 -> true
    | uu____5941 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5948 -> uu____5948
  
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
        (fun uu___88_5965  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____5976 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5976
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____6004  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____6009 =
             let uu____6012 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____6012 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____6009)
       in
    let uu____6061 =
      let uu____6064 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6064
       in
    (res, uu____6061)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6098  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6133 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6133 (fun x  -> ())  in
     (let uu____6139 =
        let uu____6144 =
          let uu____6145 = FStar_List.map mk_string old_verify_module  in
          List uu____6145  in
        ("verify_module", uu____6144)  in
      set_option' uu____6139);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6155 =
        let uu____6156 =
          let uu____6157 =
            let uu____6158 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6158  in
          (FStar_String.length f1) - uu____6157  in
        uu____6156 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6155  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6164 = get_lax ()  in
    if uu____6164
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6174 = module_name_of_file_name fn  in should_verify uu____6174
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6180 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6180
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6188 = should_verify m  in
    if uu____6188 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6196  ->
    let uu____6197 = get_no_default_includes ()  in
    if uu____6197
    then get_include ()
    else
      (let lib_paths =
         let uu____6204 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6204 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6213 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6213
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6227 =
         let uu____6230 = get_include ()  in
         FStar_List.append uu____6230 ["."]  in
       FStar_List.append lib_paths uu____6227)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____6243 = FStar_Util.smap_try_find file_map filename  in
    match uu____6243 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___90_6256  ->
               match () with
               | () ->
                   let uu____6259 = FStar_Util.is_path_absolute filename  in
                   if uu____6259
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____6266 =
                        let uu____6269 = include_path ()  in
                        FStar_List.rev uu____6269  in
                      FStar_Util.find_map uu____6266
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu____6285 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____6294  ->
    let uu____6295 = get_prims ()  in
    match uu____6295 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6299 = find_file filename  in
        (match uu____6299 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6303 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6303)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6309  ->
    let uu____6310 = prims ()  in FStar_Util.basename uu____6310
  
let (pervasives : unit -> Prims.string) =
  fun uu____6315  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____6317 = find_file filename  in
    match uu____6317 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____6321 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6321
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6326  ->
    let uu____6327 = pervasives ()  in FStar_Util.basename uu____6327
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6332  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____6334 = find_file filename  in
    match uu____6334 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____6338 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6338
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____6344 = get_odir ()  in
    match uu____6344 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____6353 = get_cache_dir ()  in
    match uu____6353 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6357 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____6357
  
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
             let uu____6423 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____6423  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____6431 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6431 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6501 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6501 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6510  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6515  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6522  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6527  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____6532  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6538 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6544 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6550 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6556 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6563  ->
    let uu____6564 = get_codegen ()  in
    FStar_Util.map_opt uu____6564
      (fun uu___84_6568  ->
         match uu___84_6568 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6569 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6578  ->
    let uu____6579 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6579
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6596  -> let uu____6597 = get_debug ()  in uu____6597 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6607 = get_debug ()  in
    FStar_All.pipe_right uu____6607 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6624 = get_debug ()  in
       FStar_All.pipe_right uu____6624 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6633  -> let uu____6634 = get_defensive ()  in uu____6634 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6639  ->
    let uu____6640 = get_defensive ()  in uu____6640 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6647  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6652  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6657  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6662  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6668 = get_dump_module ()  in
    FStar_All.pipe_right uu____6668 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6677  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6682  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6688 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6688
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6718  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6723  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6728  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6735  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6740  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6745  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6750  ->
    let uu____6751 = get_initial_fuel ()  in
    let uu____6752 = get_max_fuel ()  in Prims.min uu____6751 uu____6752
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6757  ->
    let uu____6758 = get_initial_ifuel ()  in
    let uu____6759 = get_max_ifuel ()  in Prims.min uu____6758 uu____6759
  
let (interactive : unit -> Prims.bool) =
  fun uu____6764  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6769  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6776  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6781  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6786  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6791  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6796  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6801  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6806  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6811  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6816  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6821  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6826  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6833 = get_no_extract ()  in
    FStar_All.pipe_right uu____6833
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6844  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6849  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6854  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6861  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6866  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6871  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6876  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6881  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6886  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6891  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6896  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____6901  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____6906  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6913  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____6918  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6923  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6928  ->
    let uu____6929 = get_smtencoding_nl_arith_repr ()  in
    uu____6929 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6934  ->
    let uu____6935 = get_smtencoding_nl_arith_repr ()  in
    uu____6935 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6940  ->
    let uu____6941 = get_smtencoding_nl_arith_repr ()  in
    uu____6941 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6946  ->
    let uu____6947 = get_smtencoding_l_arith_repr ()  in
    uu____6947 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6952  ->
    let uu____6953 = get_smtencoding_l_arith_repr ()  in
    uu____6953 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6958  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6963  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6968  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____6973  -> get_tactics_nbe () 
let (timing : unit -> Prims.bool) = fun uu____6978  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____6983  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____6988  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____6993  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____6998  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____7003  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____7008  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7015  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____7020  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____7033  ->
    let uu____7034 = get_using_facts_from ()  in
    match uu____7034 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7072  ->
    let uu____7073 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____7073
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7080  ->
    let uu____7081 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____7081 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7084 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7091  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____7096  ->
    let uu____7097 = get_smt ()  in
    match uu____7097 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7107  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____7112  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____7117  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7122  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____7127  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7132  ->
    (get_use_two_phase_tc ()) &&
      (let uu____7134 = lax ()  in Prims.op_Negation uu____7134)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7139  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7144  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7149  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7154  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7161 = get_extract ()  in
    match uu____7161 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7172 =
            let uu____7185 = get_no_extract ()  in
            let uu____7188 = get_extract_namespace ()  in
            let uu____7191 = get_extract_module ()  in
            (uu____7185, uu____7188, uu____7191)  in
          match uu____7172 with
          | ([],[],[]) -> ()
          | uu____7206 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7254,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7273 -> false  in
          let uu____7282 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7316  ->
                    match uu____7316 with
                    | (path,uu____7324) -> matches_path m_components path))
             in
          match uu____7282 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____7335,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____7355 = get_extract_namespace ()  in
          match uu____7355 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____7371 = get_extract_module ()  in
          match uu____7371 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____7383 = no_extract m1  in Prims.op_Negation uu____7383) &&
          (let uu____7385 =
             let uu____7394 = get_extract_namespace ()  in
             let uu____7397 = get_extract_module ()  in
             (uu____7394, uu____7397)  in
           (match uu____7385 with
            | ([],[]) -> true
            | uu____7408 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  