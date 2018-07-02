open Prims
let (debug_embedding : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
type debug_level_t =
  | Low 
  | Medium 
  | High 
  | Extreme 
  | Other of Prims.string 
let (uu___is_Low : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | Low  -> true | uu____35 -> false 
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____41 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | High  -> true | uu____47 -> false 
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____53 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____60 -> false
  
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
    match projectee with | Bool _0 -> true | uu____101 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____115 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____129 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____143 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____159 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____178 -> false
  
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
  fun projectee  -> match projectee with | Set  -> true | uu____206 -> false 
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____212 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____218 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____236  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____260  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____284  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___75_308  ->
    match uu___75_308 with
    | Bool b -> b
    | uu____310 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___76_315  ->
    match uu___76_315 with
    | Int b -> b
    | uu____317 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___77_322  ->
    match uu___77_322 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____325 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___78_332  ->
    match uu___78_332 with
    | List ts -> ts
    | uu____338 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____347 .
    (option_val -> 'Auu____347) -> option_val -> 'Auu____347 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____365 = as_list' x  in
      FStar_All.pipe_right uu____365 (FStar_List.map as_t)
  
let as_option :
  'Auu____378 .
    (option_val -> 'Auu____378) ->
      option_val -> 'Auu____378 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___79_393  ->
      match uu___79_393 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____397 = as_t v1  in FStar_Pervasives_Native.Some uu____397
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___80_404  ->
    match uu___80_404 with
    | List ls ->
        let uu____410 =
          FStar_List.map
            (fun l  ->
               let uu____420 = as_string l  in FStar_Util.split uu____420 ",")
            ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____410
    | uu____427 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let (fstar_options : optionstate Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : unit -> optionstate) =
  fun uu____453  ->
    let uu____454 = FStar_ST.op_Bang fstar_options  in
    FStar_List.hd uu____454
  
let (pop : unit -> unit) =
  fun uu____484  ->
    let uu____485 = FStar_ST.op_Bang fstar_options  in
    match uu____485 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____511::[] -> failwith "TOO MANY POPS!"
    | uu____512::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____543  ->
    let uu____544 =
      let uu____547 =
        let uu____548 = peek ()  in FStar_Util.smap_copy uu____548  in
      let uu____551 = FStar_ST.op_Bang fstar_options  in uu____547 ::
        uu____551
       in
    FStar_ST.op_Colon_Equals fstar_options uu____544
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____605 = FStar_ST.op_Bang fstar_options  in
    match uu____605 with
    | [] -> failwith "set on empty option stack"
    | uu____631::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
  
let (snapshot : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____666  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  -> let uu____686 = peek ()  in FStar_Util.smap_add uu____686 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____697  -> match uu____697 with | (k,v1) -> set_option k v1 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f ()  in pop (); retv) 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____744 =
      let uu____747 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____747
       in
    FStar_ST.op_Colon_Equals light_off_files uu____744
  
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
  ("eager_embedding", (Bool false));
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
  fun uu____1202  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1219  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1276 =
      let uu____1279 = peek ()  in FStar_Util.smap_try_find uu____1279 s  in
    match uu____1276 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1289 . Prims.string -> (option_val -> 'Auu____1289) -> 'Auu____1289
  = fun s  -> fun c  -> let uu____1305 = get_option s  in c uu____1305 
let (get_abort_on : unit -> Prims.int) =
  fun uu____1310  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1315  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1322  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1329  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1336  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1343  -> lookup_opt "cache_off" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1350  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1359  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1368  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1377  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____1384  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1391  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1398  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1403  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1408  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1415  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_embedding : unit -> Prims.bool) =
  fun uu____1422  -> lookup_opt "eager_embedding" as_bool 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1427  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1432  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1441  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1454  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1463  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1470  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1475  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1480  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1487  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1494  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1499  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1506  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1513  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1518  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1523  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1528  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1535  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1542  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1547  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1552  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1557  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1562  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1567  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1572  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1577  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1584  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1591  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1596  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1601  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1608  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1615  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1622  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1629  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1634  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1639  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1644  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1649  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1654  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1659  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1664  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1669  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1676  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1683  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1690  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1697  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1702  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1707  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1712  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1717  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1722  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____1727  -> lookup_opt "__tactics_nbe" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____1732  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1737  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1742  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1747  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1752  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1757  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1762  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1769  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1776  ->
    let uu____1777 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1777
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1786  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1799  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1808  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1817  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1824  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1829  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1836  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1843  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1848  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1853  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1858  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1863  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1868  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1873  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1878  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1883  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___81_1888  ->
    match uu___81_1888 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1900 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1906 = get_debug_level ()  in
    FStar_All.pipe_right uu____1906
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2039  ->
    let uu____2040 =
      let uu____2041 = FStar_ST.op_Bang _version  in
      let uu____2061 = FStar_ST.op_Bang _platform  in
      let uu____2081 = FStar_ST.op_Bang _compiler  in
      let uu____2101 = FStar_ST.op_Bang _date  in
      let uu____2121 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2041
        uu____2061 uu____2081 uu____2101 uu____2121
       in
    FStar_Util.print_string uu____2040
  
let display_usage_aux :
  'Auu____2147 'Auu____2148 .
    ('Auu____2147,Prims.string,'Auu____2148 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2196  ->
         match uu____2196 with
         | (uu____2207,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2219 =
                      let uu____2220 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2220  in
                    FStar_Util.print_string uu____2219
                  else
                    (let uu____2222 =
                       let uu____2223 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2223 doc  in
                     FStar_Util.print_string uu____2222)
              | FStar_Getopt.OneArg (uu____2224,argname) ->
                  if doc = ""
                  then
                    let uu____2232 =
                      let uu____2233 = FStar_Util.colorize_bold flag  in
                      let uu____2234 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2233 uu____2234
                       in
                    FStar_Util.print_string uu____2232
                  else
                    (let uu____2236 =
                       let uu____2237 = FStar_Util.colorize_bold flag  in
                       let uu____2238 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2237
                         uu____2238 doc
                        in
                     FStar_Util.print_string uu____2236))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2266 = o  in
    match uu____2266 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2302 =
                let uu____2303 = f ()  in set_option name uu____2303  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2318 = f x  in set_option name uu____2318
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2338 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2338  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2361 =
        let uu____2364 = lookup_opt name as_list'  in
        FStar_List.append uu____2364 [value]  in
      mk_list uu____2361
  
let accumulate_string :
  'Auu____2377 .
    Prims.string -> ('Auu____2377 -> Prims.string) -> 'Auu____2377 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2398 =
          let uu____2399 =
            let uu____2400 = post_processor value  in mk_string uu____2400
             in
          accumulated_option name uu____2399  in
        set_option name uu____2398
  
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
    match projectee with | Const _0 -> true | uu____2496 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2510 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2523 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2530 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2544 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2560 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2586 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2625 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2660 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2674 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2695 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2733 -> true
    | uu____2734 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2741 -> uu____2741
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2761 ->
              let uu____2762 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2762 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2766 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2766
          | PathStr uu____2769 -> mk_path str_val
          | SimpleStr uu____2770 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2775 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2790 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2790
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
            let uu____2809 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2809
  
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
    | PostProcessed (uu____2846,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2856,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2883 = desc_of_opt_type typ  in
      match uu____2883 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2889  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2906 =
      let uu____2907 = as_string s  in FStar_String.lowercase uu____2907  in
    mk_string uu____2906
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2955  ->
    let uu____2967 =
      let uu____2979 =
        let uu____2991 =
          let uu____3003 =
            let uu____3013 =
              let uu____3014 = mk_bool true  in Const uu____3014  in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____3013,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
             in
          let uu____3016 =
            let uu____3028 =
              let uu____3040 =
                let uu____3050 =
                  let uu____3051 = mk_bool true  in Const uu____3051  in
                (FStar_Getopt.noshort, "cache_off", uu____3050,
                  "Do not read or write any .checked files")
                 in
              let uu____3053 =
                let uu____3065 =
                  let uu____3077 =
                    let uu____3089 =
                      let uu____3101 =
                        let uu____3113 =
                          let uu____3125 =
                            let uu____3137 =
                              let uu____3147 =
                                let uu____3148 = mk_bool true  in
                                Const uu____3148  in
                              (FStar_Getopt.noshort, "detail_errors",
                                uu____3147,
                                "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                               in
                            let uu____3150 =
                              let uu____3162 =
                                let uu____3172 =
                                  let uu____3173 = mk_bool true  in
                                  Const uu____3173  in
                                (FStar_Getopt.noshort, "detail_hint_replay",
                                  uu____3172,
                                  "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                 in
                              let uu____3175 =
                                let uu____3187 =
                                  let uu____3197 =
                                    let uu____3198 = mk_bool true  in
                                    Const uu____3198  in
                                  (FStar_Getopt.noshort, "doc", uu____3197,
                                    "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                   in
                                let uu____3200 =
                                  let uu____3212 =
                                    let uu____3224 =
                                      let uu____3234 =
                                        let uu____3235 = mk_bool true  in
                                        Const uu____3235  in
                                      (FStar_Getopt.noshort,
                                        "eager_embedding", uu____3234,
                                        "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                       in
                                    let uu____3237 =
                                      let uu____3249 =
                                        let uu____3259 =
                                          let uu____3260 = mk_bool true  in
                                          Const uu____3260  in
                                        (FStar_Getopt.noshort,
                                          "eager_inference", uu____3259,
                                          "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                         in
                                      let uu____3262 =
                                        let uu____3274 =
                                          let uu____3284 =
                                            let uu____3285 = mk_bool true  in
                                            Const uu____3285  in
                                          (FStar_Getopt.noshort,
                                            "eager_subtyping", uu____3284,
                                            "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                           in
                                        let uu____3287 =
                                          let uu____3299 =
                                            let uu____3311 =
                                              let uu____3323 =
                                                let uu____3335 =
                                                  let uu____3345 =
                                                    let uu____3346 =
                                                      mk_bool true  in
                                                    Const uu____3346  in
                                                  (FStar_Getopt.noshort,
                                                    "expose_interfaces",
                                                    uu____3345,
                                                    "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                   in
                                                let uu____3348 =
                                                  let uu____3360 =
                                                    let uu____3370 =
                                                      let uu____3371 =
                                                        mk_bool true  in
                                                      Const uu____3371  in
                                                    (FStar_Getopt.noshort,
                                                      "hide_uvar_nums",
                                                      uu____3370,
                                                      "Don't print unification variable numbers")
                                                     in
                                                  let uu____3373 =
                                                    let uu____3385 =
                                                      let uu____3397 =
                                                        let uu____3407 =
                                                          let uu____3408 =
                                                            mk_bool true  in
                                                          Const uu____3408
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "hint_info",
                                                          uu____3407,
                                                          "Print information regarding hints (deprecated; use --query_stats instead)")
                                                         in
                                                      let uu____3410 =
                                                        let uu____3422 =
                                                          let uu____3432 =
                                                            let uu____3433 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3433
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "in", uu____3432,
                                                            "Legacy interactive mode; reads input from stdin")
                                                           in
                                                        let uu____3435 =
                                                          let uu____3447 =
                                                            let uu____3457 =
                                                              let uu____3458
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____3458
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "ide",
                                                              uu____3457,
                                                              "JSON-based interactive mode for IDEs")
                                                             in
                                                          let uu____3460 =
                                                            let uu____3472 =
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
                                                                  "indent",
                                                                  uu____3494,
                                                                  "Parses and outputs the files on the command line")
                                                                 in
                                                              let uu____3497
                                                                =
                                                                let uu____3509
                                                                  =
                                                                  let uu____3521
                                                                    =
                                                                    let uu____3533
                                                                    =
                                                                    let uu____3543
                                                                    =
                                                                    let uu____3544
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3544
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3543,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____3546
                                                                    =
                                                                    let uu____3558
                                                                    =
                                                                    let uu____3570
                                                                    =
                                                                    let uu____3580
                                                                    =
                                                                    let uu____3581
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3581
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3580,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3583
                                                                    =
                                                                    let uu____3595
                                                                    =
                                                                    let uu____3605
                                                                    =
                                                                    let uu____3606
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3606
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3605,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3608
                                                                    =
                                                                    let uu____3620
                                                                    =
                                                                    let uu____3632
                                                                    =
                                                                    let uu____3644
                                                                    =
                                                                    let uu____3656
                                                                    =
                                                                    let uu____3666
                                                                    =
                                                                    let uu____3667
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3667
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3666,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3669
                                                                    =
                                                                    let uu____3681
                                                                    =
                                                                    let uu____3693
                                                                    =
                                                                    let uu____3703
                                                                    =
                                                                    let uu____3704
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3704
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3703,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3706
                                                                    =
                                                                    let uu____3718
                                                                    =
                                                                    let uu____3730
                                                                    =
                                                                    let uu____3740
                                                                    =
                                                                    let uu____3741
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3741
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3740,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3743
                                                                    =
                                                                    let uu____3755
                                                                    =
                                                                    let uu____3765
                                                                    =
                                                                    let uu____3766
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3766
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3765,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
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
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3790,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3793
                                                                    =
                                                                    let uu____3805
                                                                    =
                                                                    let uu____3817
                                                                    =
                                                                    let uu____3829
                                                                    =
                                                                    let uu____3839
                                                                    =
                                                                    let uu____3840
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3840
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3839,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3842
                                                                    =
                                                                    let uu____3854
                                                                    =
                                                                    let uu____3864
                                                                    =
                                                                    let uu____3865
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3865
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3864,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3867
                                                                    =
                                                                    let uu____3879
                                                                    =
                                                                    let uu____3889
                                                                    =
                                                                    let uu____3890
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3890
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3889,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3892
                                                                    =
                                                                    let uu____3904
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
                                                                    "print_implicits",
                                                                    uu____3914,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3917
                                                                    =
                                                                    let uu____3929
                                                                    =
                                                                    let uu____3939
                                                                    =
                                                                    let uu____3940
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3940
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3939,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3942
                                                                    =
                                                                    let uu____3954
                                                                    =
                                                                    let uu____3964
                                                                    =
                                                                    let uu____3965
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3965
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3964,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3967
                                                                    =
                                                                    let uu____3979
                                                                    =
                                                                    let uu____3989
                                                                    =
                                                                    let uu____3990
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3990
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3989,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3992
                                                                    =
                                                                    let uu____4004
                                                                    =
                                                                    let uu____4014
                                                                    =
                                                                    let uu____4015
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4015
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____4014,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____4017
                                                                    =
                                                                    let uu____4029
                                                                    =
                                                                    let uu____4039
                                                                    =
                                                                    let uu____4040
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4040
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____4039,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____4042
                                                                    =
                                                                    let uu____4054
                                                                    =
                                                                    let uu____4066
                                                                    =
                                                                    let uu____4076
                                                                    =
                                                                    let uu____4077
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4077
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4076,
                                                                    " ")  in
                                                                    let uu____4079
                                                                    =
                                                                    let uu____4091
                                                                    =
                                                                    let uu____4103
                                                                    =
                                                                    let uu____4115
                                                                    =
                                                                    let uu____4127
                                                                    =
                                                                    let uu____4139
                                                                    =
                                                                    let uu____4149
                                                                    =
                                                                    let uu____4150
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4150
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4149,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4152
                                                                    =
                                                                    let uu____4164
                                                                    =
                                                                    let uu____4174
                                                                    =
                                                                    let uu____4175
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4175
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4174,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4177
                                                                    =
                                                                    let uu____4189
                                                                    =
                                                                    let uu____4201
                                                                    =
                                                                    let uu____4211
                                                                    =
                                                                    let uu____4212
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4212
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____4211,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____4214
                                                                    =
                                                                    let uu____4226
                                                                    =
                                                                    let uu____4236
                                                                    =
                                                                    let uu____4237
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4237
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4236,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4239
                                                                    =
                                                                    let uu____4251
                                                                    =
                                                                    let uu____4261
                                                                    =
                                                                    let uu____4262
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4262
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4261,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4264
                                                                    =
                                                                    let uu____4276
                                                                    =
                                                                    let uu____4286
                                                                    =
                                                                    let uu____4287
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4287
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4286,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4289
                                                                    =
                                                                    let uu____4301
                                                                    =
                                                                    let uu____4311
                                                                    =
                                                                    let uu____4312
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4312
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4311,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4314
                                                                    =
                                                                    let uu____4326
                                                                    =
                                                                    let uu____4336
                                                                    =
                                                                    let uu____4337
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4337
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4336,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4339
                                                                    =
                                                                    let uu____4351
                                                                    =
                                                                    let uu____4361
                                                                    =
                                                                    let uu____4362
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4362
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4361,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4364
                                                                    =
                                                                    let uu____4376
                                                                    =
                                                                    let uu____4386
                                                                    =
                                                                    let uu____4387
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4387
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4386,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4389
                                                                    =
                                                                    let uu____4401
                                                                    =
                                                                    let uu____4411
                                                                    =
                                                                    let uu____4412
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4412
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4411,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4414
                                                                    =
                                                                    let uu____4426
                                                                    =
                                                                    let uu____4438
                                                                    =
                                                                    let uu____4448
                                                                    =
                                                                    let uu____4449
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4449
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4448,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4451
                                                                    =
                                                                    let uu____4463
                                                                    =
                                                                    let uu____4475
                                                                    =
                                                                    let uu____4487
                                                                    =
                                                                    let uu____4499
                                                                    =
                                                                    let uu____4509
                                                                    =
                                                                    let uu____4510
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4510
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4509,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4512
                                                                    =
                                                                    let uu____4524
                                                                    =
                                                                    let uu____4534
                                                                    =
                                                                    let uu____4535
                                                                    =
                                                                    let uu____4543
                                                                    =
                                                                    let uu____4544
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4544
                                                                     in
                                                                    ((fun
                                                                    uu____4550
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4543)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4535
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4534,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4554
                                                                    =
                                                                    let uu____4566
                                                                    =
                                                                    let uu____4576
                                                                    =
                                                                    let uu____4577
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4577
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4576,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4579
                                                                    =
                                                                    let uu____4591
                                                                    =
                                                                    let uu____4603
                                                                    =
                                                                    let uu____4613
                                                                    =
                                                                    let uu____4614
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4614
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4613,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4616
                                                                    =
                                                                    let uu____4628
                                                                    =
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
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4687
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4686,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4689
                                                                    =
                                                                    let uu____4701
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
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4711,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4714
                                                                    =
                                                                    let uu____4726
                                                                    =
                                                                    let uu____4738
                                                                    =
                                                                    let uu____4750
                                                                    =
                                                                    let uu____4760
                                                                    =
                                                                    let uu____4761
                                                                    =
                                                                    let uu____4769
                                                                    =
                                                                    let uu____4770
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4770
                                                                     in
                                                                    ((fun
                                                                    uu____4775
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____4769)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4761
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____4760,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____4796
                                                                    =
                                                                    let uu____4808
                                                                    =
                                                                    let uu____4818
                                                                    =
                                                                    let uu____4819
                                                                    =
                                                                    let uu____4827
                                                                    =
                                                                    let uu____4828
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4828
                                                                     in
                                                                    ((fun
                                                                    uu____4834
                                                                     ->
                                                                    (
                                                                    let uu____4836
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4836);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4827)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4819
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4818,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4808]
                                                                     in
                                                                    uu____4750
                                                                    ::
                                                                    uu____4796
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4738
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4726
                                                                     in
                                                                    uu____4701
                                                                    ::
                                                                    uu____4714
                                                                     in
                                                                    uu____4676
                                                                    ::
                                                                    uu____4689
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4664
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4652
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4640
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4628
                                                                     in
                                                                    uu____4603
                                                                    ::
                                                                    uu____4616
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4591
                                                                     in
                                                                    uu____4566
                                                                    ::
                                                                    uu____4579
                                                                     in
                                                                    uu____4524
                                                                    ::
                                                                    uu____4554
                                                                     in
                                                                    uu____4499
                                                                    ::
                                                                    uu____4512
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4487
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4475
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4463
                                                                     in
                                                                    uu____4438
                                                                    ::
                                                                    uu____4451
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4426
                                                                     in
                                                                    uu____4401
                                                                    ::
                                                                    uu____4414
                                                                     in
                                                                    uu____4376
                                                                    ::
                                                                    uu____4389
                                                                     in
                                                                    uu____4351
                                                                    ::
                                                                    uu____4364
                                                                     in
                                                                    uu____4326
                                                                    ::
                                                                    uu____4339
                                                                     in
                                                                    uu____4301
                                                                    ::
                                                                    uu____4314
                                                                     in
                                                                    uu____4276
                                                                    ::
                                                                    uu____4289
                                                                     in
                                                                    uu____4251
                                                                    ::
                                                                    uu____4264
                                                                     in
                                                                    uu____4226
                                                                    ::
                                                                    uu____4239
                                                                     in
                                                                    uu____4201
                                                                    ::
                                                                    uu____4214
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4189
                                                                     in
                                                                    uu____4164
                                                                    ::
                                                                    uu____4177
                                                                     in
                                                                    uu____4139
                                                                    ::
                                                                    uu____4152
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4127
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4115
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4103
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4091
                                                                     in
                                                                    uu____4066
                                                                    ::
                                                                    uu____4079
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____4054
                                                                     in
                                                                    uu____4029
                                                                    ::
                                                                    uu____4042
                                                                     in
                                                                    uu____4004
                                                                    ::
                                                                    uu____4017
                                                                     in
                                                                    uu____3979
                                                                    ::
                                                                    uu____3992
                                                                     in
                                                                    uu____3954
                                                                    ::
                                                                    uu____3967
                                                                     in
                                                                    uu____3929
                                                                    ::
                                                                    uu____3942
                                                                     in
                                                                    uu____3904
                                                                    ::
                                                                    uu____3917
                                                                     in
                                                                    uu____3879
                                                                    ::
                                                                    uu____3892
                                                                     in
                                                                    uu____3854
                                                                    ::
                                                                    uu____3867
                                                                     in
                                                                    uu____3829
                                                                    ::
                                                                    uu____3842
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3817
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3805
                                                                     in
                                                                    uu____3780
                                                                    ::
                                                                    uu____3793
                                                                     in
                                                                    uu____3755
                                                                    ::
                                                                    uu____3768
                                                                     in
                                                                    uu____3730
                                                                    ::
                                                                    uu____3743
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3718
                                                                     in
                                                                    uu____3693
                                                                    ::
                                                                    uu____3706
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3681
                                                                     in
                                                                    uu____3656
                                                                    ::
                                                                    uu____3669
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3644
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3632
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3620
                                                                     in
                                                                    uu____3595
                                                                    ::
                                                                    uu____3608
                                                                     in
                                                                    uu____3570
                                                                    ::
                                                                    uu____3583
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3558
                                                                     in
                                                                    uu____3533
                                                                    ::
                                                                    uu____3546
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (
                                                                    IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____3521
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_fuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of recursive functions to try initially (default 2)")
                                                                  ::
                                                                  uu____3509
                                                                 in
                                                              uu____3484 ::
                                                                uu____3497
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "include",
                                                              (ReverseAccumulated
                                                                 (PathStr
                                                                    "path")),
                                                              "A directory in which to search for files included on the command line")
                                                              :: uu____3472
                                                             in
                                                          uu____3447 ::
                                                            uu____3460
                                                           in
                                                        uu____3422 ::
                                                          uu____3435
                                                         in
                                                      uu____3397 ::
                                                        uu____3410
                                                       in
                                                    (FStar_Getopt.noshort,
                                                      "hint_file",
                                                      (PathStr "path"),
                                                      "Read/write hints to <path> (instead of module-specific hints files)")
                                                      :: uu____3385
                                                     in
                                                  uu____3360 :: uu____3373
                                                   in
                                                uu____3335 :: uu____3348  in
                                              (FStar_Getopt.noshort,
                                                "extract_namespace",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "namespace name")))),
                                                "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                :: uu____3323
                                               in
                                            (FStar_Getopt.noshort,
                                              "extract_module",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "module_name")))),
                                              "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                              :: uu____3311
                                             in
                                          (FStar_Getopt.noshort, "extract",
                                            (Accumulated
                                               (SimpleStr
                                                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                            "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                            :: uu____3299
                                           in
                                        uu____3274 :: uu____3287  in
                                      uu____3249 :: uu____3262  in
                                    uu____3224 :: uu____3237  in
                                  (FStar_Getopt.noshort, "dump_module",
                                    (Accumulated (SimpleStr "module_name")),
                                    "") :: uu____3212
                                   in
                                uu____3187 :: uu____3200  in
                              uu____3162 :: uu____3175  in
                            uu____3137 :: uu____3150  in
                          (FStar_Getopt.noshort, "dep",
                            (EnumStr ["make"; "graph"; "full"]),
                            "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                            :: uu____3125
                           in
                        (FStar_Getopt.noshort, "defensive",
                          (EnumStr ["no"; "warn"; "fail"]),
                          "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                          :: uu____3113
                         in
                      (FStar_Getopt.noshort, "debug_level",
                        (Accumulated
                           (OpenEnumStr
                              (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                        "Control the verbosity of debugging info") ::
                        uu____3101
                       in
                    (FStar_Getopt.noshort, "debug",
                      (Accumulated (SimpleStr "module_name")),
                      "Print lots of debugging information while checking module")
                      :: uu____3089
                     in
                  (FStar_Getopt.noshort, "codegen-lib",
                    (Accumulated (SimpleStr "namespace")),
                    "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                    :: uu____3077
                   in
                (FStar_Getopt.noshort, "codegen",
                  (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                  "Generate code for further compilation to executable code, or build a compiler plugin")
                  :: uu____3065
                 in
              uu____3040 :: uu____3053  in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____3028
             in
          uu____3003 :: uu____3016  in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____2991
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____2979
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___82_5780  ->
             match uu___82_5780 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____2967

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5803  ->
    let uu____5806 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5833  ->
         match uu____5833 with
         | (short,long,typ,doc) ->
             let uu____5849 =
               let uu____5861 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5861, doc)  in
             mk_spec uu____5849) uu____5806

let (settable : Prims.string -> Prims.bool) =
  fun uu___83_5871  ->
    match uu___83_5871 with
    | "abort_on" -> true
    | "admit_smt_queries" -> true
    | "admit_except" -> true
    | "debug" -> true
    | "debug_level" -> true
    | "defensive" -> true
    | "detail_errors" -> true
    | "detail_hint_replay" -> true
    | "eager_embedding" -> true
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
    | uu____5872 -> false
  
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
       (fun uu____5946  ->
          match uu____5946 with
          | (uu____5958,x,uu____5960,uu____5961) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____6023  ->
          match uu____6023 with
          | (uu____6035,x,uu____6037,uu____6038) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____6049  ->
    let uu____6050 = specs ()  in display_usage_aux uu____6050
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____6074 -> true
    | uu____6075 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____6082 -> uu____6082
  
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
          let uu____6110 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____6110
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____6138  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____6143 =
             let uu____6146 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____6146 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____6143)
       in
    let uu____6195 =
      let uu____6198 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6198
       in
    (res, uu____6195)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6232  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6267 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6267 (fun x  -> ())  in
     (let uu____6273 =
        let uu____6278 =
          let uu____6279 = FStar_List.map mk_string old_verify_module  in
          List uu____6279  in
        ("verify_module", uu____6278)  in
      set_option' uu____6273);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6289 =
        let uu____6290 =
          let uu____6291 =
            let uu____6292 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6292  in
          (FStar_String.length f1) - uu____6291  in
        uu____6290 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6289  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6298 = get_lax ()  in
    if uu____6298
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6308 = module_name_of_file_name fn  in should_verify uu____6308
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6314 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6314
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6322 = should_verify m  in
    if uu____6322 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6330  ->
    let uu____6331 = get_no_default_includes ()  in
    if uu____6331
    then get_include ()
    else
      (let lib_paths =
         let uu____6338 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6338 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6347 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6347
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6361 =
         let uu____6364 = get_include ()  in
         FStar_List.append uu____6364 ["."]  in
       FStar_List.append lib_paths uu____6361)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____6377 = FStar_Util.smap_try_find file_map filename  in
    match uu____6377 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            let uu____6393 = FStar_Util.is_path_absolute filename  in
            if uu____6393
            then
              (if FStar_Util.file_exists filename
               then FStar_Pervasives_Native.Some filename
               else FStar_Pervasives_Native.None)
            else
              (let uu____6400 =
                 let uu____6403 = include_path ()  in
                 FStar_List.rev uu____6403  in
               FStar_Util.find_map uu____6400
                 (fun p  ->
                    let path =
                      if p = "."
                      then filename
                      else FStar_Util.join_paths p filename  in
                    if FStar_Util.file_exists path
                    then FStar_Pervasives_Native.Some path
                    else FStar_Pervasives_Native.None))
          with | uu____6419 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____6428  ->
    let uu____6429 = get_prims ()  in
    match uu____6429 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6433 = find_file filename  in
        (match uu____6433 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6437 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6437)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6443  ->
    let uu____6444 = prims ()  in FStar_Util.basename uu____6444
  
let (pervasives : unit -> Prims.string) =
  fun uu____6449  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____6451 = find_file filename  in
    match uu____6451 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____6455 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6455
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6460  ->
    let uu____6461 = pervasives ()  in FStar_Util.basename uu____6461
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6466  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____6468 = find_file filename  in
    match uu____6468 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____6472 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6472
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____6478 = get_odir ()  in
    match uu____6478 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____6487 = get_cache_dir ()  in
    match uu____6487 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6491 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____6491
  
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
             let uu____6557 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____6557  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____6565 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6565 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6635 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6635 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6644  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6649  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6656  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6661  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____6666  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6672 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6678 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6684 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6690 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6697  ->
    let uu____6698 = get_codegen ()  in
    FStar_Util.map_opt uu____6698
      (fun uu___84_6702  ->
         match uu___84_6702 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6703 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6712  ->
    let uu____6713 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6713
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6730  -> let uu____6731 = get_debug ()  in uu____6731 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6741 = get_debug ()  in
    FStar_All.pipe_right uu____6741 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6758 = get_debug ()  in
       FStar_All.pipe_right uu____6758 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6767  -> let uu____6768 = get_defensive ()  in uu____6768 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6773  ->
    let uu____6774 = get_defensive ()  in uu____6774 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6781  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6786  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6791  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6796  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6802 = get_dump_module ()  in
    FStar_All.pipe_right uu____6802 (FStar_List.contains s)
  
let (eager_embedding : unit -> Prims.bool) =
  fun uu____6811  -> get_eager_embedding () 
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6816  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6821  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6827 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6827
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6857  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6862  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6867  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6874  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6879  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6884  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6889  ->
    let uu____6890 = get_initial_fuel ()  in
    let uu____6891 = get_max_fuel ()  in Prims.min uu____6890 uu____6891
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6896  ->
    let uu____6897 = get_initial_ifuel ()  in
    let uu____6898 = get_max_ifuel ()  in Prims.min uu____6897 uu____6898
  
let (interactive : unit -> Prims.bool) =
  fun uu____6903  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6908  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6915  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6920  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6925  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6930  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6935  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6940  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6945  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6950  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6955  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6960  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6965  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6972 = get_no_extract ()  in
    FStar_All.pipe_right uu____6972
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6983  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6988  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6993  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7000  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____7005  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____7010  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____7015  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____7020  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____7025  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____7030  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____7035  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____7040  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____7045  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7052  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____7057  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____7062  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____7067  ->
    let uu____7068 = get_smtencoding_nl_arith_repr ()  in
    uu____7068 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____7073  ->
    let uu____7074 = get_smtencoding_nl_arith_repr ()  in
    uu____7074 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____7079  ->
    let uu____7080 = get_smtencoding_nl_arith_repr ()  in
    uu____7080 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____7085  ->
    let uu____7086 = get_smtencoding_l_arith_repr ()  in
    uu____7086 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____7091  ->
    let uu____7092 = get_smtencoding_l_arith_repr ()  in
    uu____7092 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____7097  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____7102  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____7107  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____7112  -> get_tactics_nbe () 
let (timing : unit -> Prims.bool) = fun uu____7117  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____7122  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____7127  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____7132  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____7137  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____7142  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____7147  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7154  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____7159  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____7172  ->
    let uu____7173 = get_using_facts_from ()  in
    match uu____7173 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7211  ->
    let uu____7212 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____7212
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7219  ->
    let uu____7220 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____7220 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7223 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7230  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____7235  ->
    let uu____7236 = get_smt ()  in
    match uu____7236 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7246  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____7251  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____7256  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7261  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____7266  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7271  ->
    (get_use_two_phase_tc ()) &&
      (let uu____7273 = lax ()  in Prims.op_Negation uu____7273)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7278  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7283  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7288  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7293  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7300 = get_extract ()  in
    match uu____7300 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7311 =
            let uu____7324 = get_no_extract ()  in
            let uu____7327 = get_extract_namespace ()  in
            let uu____7330 = get_extract_module ()  in
            (uu____7324, uu____7327, uu____7330)  in
          match uu____7311 with
          | ([],[],[]) -> ()
          | uu____7345 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7393,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7412 -> false  in
          let uu____7421 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7455  ->
                    match uu____7455 with
                    | (path,uu____7463) -> matches_path m_components path))
             in
          match uu____7421 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____7474,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____7494 = get_extract_namespace ()  in
          match uu____7494 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____7510 = get_extract_module ()  in
          match uu____7510 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____7522 = no_extract m1  in Prims.op_Negation uu____7522) &&
          (let uu____7524 =
             let uu____7533 = get_extract_namespace ()  in
             let uu____7536 = get_extract_module ()  in
             (uu____7533, uu____7536)  in
           (match uu____7524 with
            | ([],[]) -> true
            | uu____7547 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  