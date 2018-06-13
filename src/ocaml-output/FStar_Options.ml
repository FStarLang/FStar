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
  fun uu___74_296  ->
    match uu___74_296 with
    | Bool b -> b
    | uu____298 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___75_303  ->
    match uu___75_303 with
    | Int b -> b
    | uu____305 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___76_310  ->
    match uu___76_310 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____313 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___77_320  ->
    match uu___77_320 with
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
    fun uu___78_381  ->
      match uu___78_381 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____385 = as_t v1  in FStar_Pervasives_Native.Some uu____385
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___79_392  ->
    match uu___79_392 with
    | List ls ->
        let uu____398 =
          FStar_List.map
            (fun l  ->
               let uu____408 = as_string l  in FStar_Util.split uu____408 ",")
            ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____398
    | uu____415 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let (fstar_options : optionstate Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : unit -> optionstate) =
  fun uu____441  ->
    let uu____442 = FStar_ST.op_Bang fstar_options  in
    FStar_List.hd uu____442
  
let (pop : unit -> unit) =
  fun uu____476  ->
    let uu____477 = FStar_ST.op_Bang fstar_options  in
    match uu____477 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____507::[] -> failwith "TOO MANY POPS!"
    | uu____508::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
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
    let uu____613 = FStar_ST.op_Bang fstar_options  in
    match uu____613 with
    | [] -> failwith "set on empty option stack"
    | uu____643::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
  
let (snapshot : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____682  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  -> let uu____702 = peek ()  in FStar_Util.smap_add uu____702 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____713  -> match uu____713 with | (k,v1) -> set_option k v1 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f ()  in pop (); retv) 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____760 =
      let uu____763 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____763
       in
    FStar_ST.op_Colon_Equals light_off_files uu____760
  
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
  fun uu____1214  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1231  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1296 =
      let uu____1299 = peek ()  in FStar_Util.smap_try_find uu____1299 s  in
    match uu____1296 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1309 . Prims.string -> (option_val -> 'Auu____1309) -> 'Auu____1309
  = fun s  -> fun c  -> let uu____1325 = get_option s  in c uu____1325 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1330  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1337  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1344  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1351  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1358  -> lookup_opt "cache_off" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1365  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1374  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1383  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1392  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____1399  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1406  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1413  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1418  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1423  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1430  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1437  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1442  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1451  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1464  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1473  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1480  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1485  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1490  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1497  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1504  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1509  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1516  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1523  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1528  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1533  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1538  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1545  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1552  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1557  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1562  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1567  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1572  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1577  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1582  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1587  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1594  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1601  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1606  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1611  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1618  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1625  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1632  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1639  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1644  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1649  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1654  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1659  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1664  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1669  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1674  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1679  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1686  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1693  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1700  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1707  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1712  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1717  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1722  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1727  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1732  -> lookup_opt "tactic_trace_d" as_int 
let (get_timing : unit -> Prims.bool) =
  fun uu____1737  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1742  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1747  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1752  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1757  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1762  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1767  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1774  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1781  ->
    let uu____1782 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1782
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1791  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1804  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1813  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1822  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1829  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1834  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1841  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1848  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1853  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1858  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1863  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1868  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1873  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1878  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1883  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1888  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___80_1893  ->
    match uu___80_1893 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1905 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1911 = get_debug_level ()  in
    FStar_All.pipe_right uu____1911
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2044  ->
    let uu____2045 =
      let uu____2046 = FStar_ST.op_Bang _version  in
      let uu____2070 = FStar_ST.op_Bang _platform  in
      let uu____2094 = FStar_ST.op_Bang _compiler  in
      let uu____2118 = FStar_ST.op_Bang _date  in
      let uu____2142 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2046
        uu____2070 uu____2094 uu____2118 uu____2142
       in
    FStar_Util.print_string uu____2045
  
let display_usage_aux :
  'Auu____2172 'Auu____2173 .
    ('Auu____2172,Prims.string,'Auu____2173 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2221  ->
         match uu____2221 with
         | (uu____2232,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2244 =
                      let uu____2245 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2245  in
                    FStar_Util.print_string uu____2244
                  else
                    (let uu____2247 =
                       let uu____2248 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2248 doc  in
                     FStar_Util.print_string uu____2247)
              | FStar_Getopt.OneArg (uu____2249,argname) ->
                  if doc = ""
                  then
                    let uu____2257 =
                      let uu____2258 = FStar_Util.colorize_bold flag  in
                      let uu____2259 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2258 uu____2259
                       in
                    FStar_Util.print_string uu____2257
                  else
                    (let uu____2261 =
                       let uu____2262 = FStar_Util.colorize_bold flag  in
                       let uu____2263 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2262
                         uu____2263 doc
                        in
                     FStar_Util.print_string uu____2261))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2291 = o  in
    match uu____2291 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2327 =
                let uu____2328 = f ()  in set_option name uu____2328  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2343 = f x  in set_option name uu____2343
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2363 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2363  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2386 =
        let uu____2389 = lookup_opt name as_list'  in
        FStar_List.append uu____2389 [value]  in
      mk_list uu____2386
  
let accumulate_string :
  'Auu____2402 .
    Prims.string -> ('Auu____2402 -> Prims.string) -> 'Auu____2402 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2423 =
          let uu____2424 =
            let uu____2425 = post_processor value  in mk_string uu____2425
             in
          accumulated_option name uu____2424  in
        set_option name uu____2423
  
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
    match projectee with | Const _0 -> true | uu____2521 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2535 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2548 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2555 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2569 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2585 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2611 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2650 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2685 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2699 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2720 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2758 -> true
    | uu____2759 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2766 -> uu____2766
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2786 ->
              let uu____2787 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2787 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2791 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2791
          | PathStr uu____2794 -> mk_path str_val
          | SimpleStr uu____2795 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2800 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2815 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2815
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
            let uu____2834 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2834
  
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
    | PostProcessed (uu____2871,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2881,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2908 = desc_of_opt_type typ  in
      match uu____2908 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2914  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2931 =
      let uu____2932 = as_string s  in FStar_String.lowercase uu____2932  in
    mk_string uu____2931
  
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2954  ->
    let uu____2966 =
      let uu____2978 =
        let uu____2990 =
          let uu____3000 = let uu____3001 = mk_bool true  in Const uu____3001
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____3000,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
           in
        let uu____3003 =
          let uu____3015 =
            let uu____3027 =
              let uu____3037 =
                let uu____3038 = mk_bool true  in Const uu____3038  in
              (FStar_Getopt.noshort, "cache_off", uu____3037,
                "Do not read or write any .checked files")
               in
            let uu____3040 =
              let uu____3052 =
                let uu____3064 =
                  let uu____3076 =
                    let uu____3088 =
                      let uu____3100 =
                        let uu____3112 =
                          let uu____3124 =
                            let uu____3134 =
                              let uu____3135 = mk_bool true  in
                              Const uu____3135  in
                            (FStar_Getopt.noshort, "detail_errors",
                              uu____3134,
                              "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                             in
                          let uu____3137 =
                            let uu____3149 =
                              let uu____3159 =
                                let uu____3160 = mk_bool true  in
                                Const uu____3160  in
                              (FStar_Getopt.noshort, "detail_hint_replay",
                                uu____3159,
                                "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                               in
                            let uu____3162 =
                              let uu____3174 =
                                let uu____3184 =
                                  let uu____3185 = mk_bool true  in
                                  Const uu____3185  in
                                (FStar_Getopt.noshort, "doc", uu____3184,
                                  "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                 in
                              let uu____3187 =
                                let uu____3199 =
                                  let uu____3211 =
                                    let uu____3221 =
                                      let uu____3222 = mk_bool true  in
                                      Const uu____3222  in
                                    (FStar_Getopt.noshort, "eager_inference",
                                      uu____3221,
                                      "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                     in
                                  let uu____3224 =
                                    let uu____3236 =
                                      let uu____3246 =
                                        let uu____3247 = mk_bool true  in
                                        Const uu____3247  in
                                      (FStar_Getopt.noshort,
                                        "eager_subtyping", uu____3246,
                                        "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                       in
                                    let uu____3249 =
                                      let uu____3261 =
                                        let uu____3273 =
                                          let uu____3285 =
                                            let uu____3297 =
                                              let uu____3307 =
                                                let uu____3308 = mk_bool true
                                                   in
                                                Const uu____3308  in
                                              (FStar_Getopt.noshort,
                                                "expose_interfaces",
                                                uu____3307,
                                                "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                               in
                                            let uu____3310 =
                                              let uu____3322 =
                                                let uu____3332 =
                                                  let uu____3333 =
                                                    mk_bool true  in
                                                  Const uu____3333  in
                                                (FStar_Getopt.noshort,
                                                  "hide_uvar_nums",
                                                  uu____3332,
                                                  "Don't print unification variable numbers")
                                                 in
                                              let uu____3335 =
                                                let uu____3347 =
                                                  let uu____3359 =
                                                    let uu____3369 =
                                                      let uu____3370 =
                                                        mk_bool true  in
                                                      Const uu____3370  in
                                                    (FStar_Getopt.noshort,
                                                      "hint_info",
                                                      uu____3369,
                                                      "Print information regarding hints (deprecated; use --query_stats instead)")
                                                     in
                                                  let uu____3372 =
                                                    let uu____3384 =
                                                      let uu____3394 =
                                                        let uu____3395 =
                                                          mk_bool true  in
                                                        Const uu____3395  in
                                                      (FStar_Getopt.noshort,
                                                        "in", uu____3394,
                                                        "Legacy interactive mode; reads input from stdin")
                                                       in
                                                    let uu____3397 =
                                                      let uu____3409 =
                                                        let uu____3419 =
                                                          let uu____3420 =
                                                            mk_bool true  in
                                                          Const uu____3420
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "ide", uu____3419,
                                                          "JSON-based interactive mode for IDEs")
                                                         in
                                                      let uu____3422 =
                                                        let uu____3434 =
                                                          let uu____3446 =
                                                            let uu____3456 =
                                                              let uu____3457
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____3457
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "indent",
                                                              uu____3456,
                                                              "Parses and outputs the files on the command line")
                                                             in
                                                          let uu____3459 =
                                                            let uu____3471 =
                                                              let uu____3483
                                                                =
                                                                let uu____3495
                                                                  =
                                                                  let uu____3505
                                                                    =
                                                                    let uu____3506
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3506
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3505,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                   in
                                                                let uu____3508
                                                                  =
                                                                  let uu____3520
                                                                    =
                                                                    let uu____3532
                                                                    =
                                                                    let uu____3542
                                                                    =
                                                                    let uu____3543
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3543
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3542,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3545
                                                                    =
                                                                    let uu____3557
                                                                    =
                                                                    let uu____3567
                                                                    =
                                                                    let uu____3568
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3568
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3567,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3570
                                                                    =
                                                                    let uu____3582
                                                                    =
                                                                    let uu____3594
                                                                    =
                                                                    let uu____3606
                                                                    =
                                                                    let uu____3618
                                                                    =
                                                                    let uu____3628
                                                                    =
                                                                    let uu____3629
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3629
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3628,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3631
                                                                    =
                                                                    let uu____3643
                                                                    =
                                                                    let uu____3655
                                                                    =
                                                                    let uu____3665
                                                                    =
                                                                    let uu____3666
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3666
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3665,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3668
                                                                    =
                                                                    let uu____3680
                                                                    =
                                                                    let uu____3692
                                                                    =
                                                                    let uu____3702
                                                                    =
                                                                    let uu____3703
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3703
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3702,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3705
                                                                    =
                                                                    let uu____3717
                                                                    =
                                                                    let uu____3727
                                                                    =
                                                                    let uu____3728
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3728
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3727,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3730
                                                                    =
                                                                    let uu____3742
                                                                    =
                                                                    let uu____3752
                                                                    =
                                                                    let uu____3753
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3753
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3752,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3755
                                                                    =
                                                                    let uu____3767
                                                                    =
                                                                    let uu____3779
                                                                    =
                                                                    let uu____3791
                                                                    =
                                                                    let uu____3801
                                                                    =
                                                                    let uu____3802
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3802
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3801,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3804
                                                                    =
                                                                    let uu____3816
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
                                                                    "print_effect_args",
                                                                    uu____3826,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3829
                                                                    =
                                                                    let uu____3841
                                                                    =
                                                                    let uu____3851
                                                                    =
                                                                    let uu____3852
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3852
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3851,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3854
                                                                    =
                                                                    let uu____3866
                                                                    =
                                                                    let uu____3876
                                                                    =
                                                                    let uu____3877
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3877
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3876,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3879
                                                                    =
                                                                    let uu____3891
                                                                    =
                                                                    let uu____3901
                                                                    =
                                                                    let uu____3902
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3902
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3901,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3904
                                                                    =
                                                                    let uu____3916
                                                                    =
                                                                    let uu____3926
                                                                    =
                                                                    let uu____3927
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3927
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3926,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3929
                                                                    =
                                                                    let uu____3941
                                                                    =
                                                                    let uu____3951
                                                                    =
                                                                    let uu____3952
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3952
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3951,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3954
                                                                    =
                                                                    let uu____3966
                                                                    =
                                                                    let uu____3976
                                                                    =
                                                                    let uu____3977
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3977
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3976,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3979
                                                                    =
                                                                    let uu____3991
                                                                    =
                                                                    let uu____4001
                                                                    =
                                                                    let uu____4002
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4002
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____4001,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____4004
                                                                    =
                                                                    let uu____4016
                                                                    =
                                                                    let uu____4028
                                                                    =
                                                                    let uu____4038
                                                                    =
                                                                    let uu____4039
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4039
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4038,
                                                                    " ")  in
                                                                    let uu____4041
                                                                    =
                                                                    let uu____4053
                                                                    =
                                                                    let uu____4065
                                                                    =
                                                                    let uu____4077
                                                                    =
                                                                    let uu____4089
                                                                    =
                                                                    let uu____4101
                                                                    =
                                                                    let uu____4111
                                                                    =
                                                                    let uu____4112
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4112
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4111,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4114
                                                                    =
                                                                    let uu____4126
                                                                    =
                                                                    let uu____4136
                                                                    =
                                                                    let uu____4137
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4137
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4136,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4139
                                                                    =
                                                                    let uu____4151
                                                                    =
                                                                    let uu____4163
                                                                    =
                                                                    let uu____4173
                                                                    =
                                                                    let uu____4174
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4174
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4173,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4176
                                                                    =
                                                                    let uu____4188
                                                                    =
                                                                    let uu____4198
                                                                    =
                                                                    let uu____4199
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4199
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4198,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4201
                                                                    =
                                                                    let uu____4213
                                                                    =
                                                                    let uu____4223
                                                                    =
                                                                    let uu____4224
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4224
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4223,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4226
                                                                    =
                                                                    let uu____4238
                                                                    =
                                                                    let uu____4248
                                                                    =
                                                                    let uu____4249
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4249
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4248,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4251
                                                                    =
                                                                    let uu____4263
                                                                    =
                                                                    let uu____4273
                                                                    =
                                                                    let uu____4274
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4274
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4273,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4276
                                                                    =
                                                                    let uu____4288
                                                                    =
                                                                    let uu____4298
                                                                    =
                                                                    let uu____4299
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4299
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4298,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4301
                                                                    =
                                                                    let uu____4313
                                                                    =
                                                                    let uu____4323
                                                                    =
                                                                    let uu____4324
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4324
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4323,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4326
                                                                    =
                                                                    let uu____4338
                                                                    =
                                                                    let uu____4348
                                                                    =
                                                                    let uu____4349
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4349
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4348,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4351
                                                                    =
                                                                    let uu____4363
                                                                    =
                                                                    let uu____4375
                                                                    =
                                                                    let uu____4385
                                                                    =
                                                                    let uu____4386
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4386
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4385,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4388
                                                                    =
                                                                    let uu____4400
                                                                    =
                                                                    let uu____4412
                                                                    =
                                                                    let uu____4424
                                                                    =
                                                                    let uu____4436
                                                                    =
                                                                    let uu____4446
                                                                    =
                                                                    let uu____4447
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4447
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4446,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4449
                                                                    =
                                                                    let uu____4461
                                                                    =
                                                                    let uu____4471
                                                                    =
                                                                    let uu____4472
                                                                    =
                                                                    let uu____4480
                                                                    =
                                                                    let uu____4481
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4481
                                                                     in
                                                                    ((fun
                                                                    uu____4487
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4480)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4472
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4471,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4491
                                                                    =
                                                                    let uu____4503
                                                                    =
                                                                    let uu____4513
                                                                    =
                                                                    let uu____4514
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4514
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4513,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4516
                                                                    =
                                                                    let uu____4528
                                                                    =
                                                                    let uu____4540
                                                                    =
                                                                    let uu____4550
                                                                    =
                                                                    let uu____4551
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4551
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4550,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4553
                                                                    =
                                                                    let uu____4565
                                                                    =
                                                                    let uu____4577
                                                                    =
                                                                    let uu____4589
                                                                    =
                                                                    let uu____4601
                                                                    =
                                                                    let uu____4613
                                                                    =
                                                                    let uu____4623
                                                                    =
                                                                    let uu____4624
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4624
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4623,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4626
                                                                    =
                                                                    let uu____4638
                                                                    =
                                                                    let uu____4648
                                                                    =
                                                                    let uu____4649
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4649
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4648,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4651
                                                                    =
                                                                    let uu____4663
                                                                    =
                                                                    let uu____4675
                                                                    =
                                                                    let uu____4687
                                                                    =
                                                                    let uu____4697
                                                                    =
                                                                    let uu____4698
                                                                    =
                                                                    let uu____4706
                                                                    =
                                                                    let uu____4707
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4707
                                                                     in
                                                                    ((fun
                                                                    uu____4713
                                                                     ->
                                                                    (
                                                                    let uu____4715
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4715);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4706)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4698
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4697,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4687]
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4675
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4663
                                                                     in
                                                                    uu____4638
                                                                    ::
                                                                    uu____4651
                                                                     in
                                                                    uu____4613
                                                                    ::
                                                                    uu____4626
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4601
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4589
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4577
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4565
                                                                     in
                                                                    uu____4540
                                                                    ::
                                                                    uu____4553
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4528
                                                                     in
                                                                    uu____4503
                                                                    ::
                                                                    uu____4516
                                                                     in
                                                                    uu____4461
                                                                    ::
                                                                    uu____4491
                                                                     in
                                                                    uu____4436
                                                                    ::
                                                                    uu____4449
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4424
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4412
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4400
                                                                     in
                                                                    uu____4375
                                                                    ::
                                                                    uu____4388
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4363
                                                                     in
                                                                    uu____4338
                                                                    ::
                                                                    uu____4351
                                                                     in
                                                                    uu____4313
                                                                    ::
                                                                    uu____4326
                                                                     in
                                                                    uu____4288
                                                                    ::
                                                                    uu____4301
                                                                     in
                                                                    uu____4263
                                                                    ::
                                                                    uu____4276
                                                                     in
                                                                    uu____4238
                                                                    ::
                                                                    uu____4251
                                                                     in
                                                                    uu____4213
                                                                    ::
                                                                    uu____4226
                                                                     in
                                                                    uu____4188
                                                                    ::
                                                                    uu____4201
                                                                     in
                                                                    uu____4163
                                                                    ::
                                                                    uu____4176
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4151
                                                                     in
                                                                    uu____4126
                                                                    ::
                                                                    uu____4139
                                                                     in
                                                                    uu____4101
                                                                    ::
                                                                    uu____4114
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4089
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4077
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4065
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4053
                                                                     in
                                                                    uu____4028
                                                                    ::
                                                                    uu____4041
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____4016
                                                                     in
                                                                    uu____3991
                                                                    ::
                                                                    uu____4004
                                                                     in
                                                                    uu____3966
                                                                    ::
                                                                    uu____3979
                                                                     in
                                                                    uu____3941
                                                                    ::
                                                                    uu____3954
                                                                     in
                                                                    uu____3916
                                                                    ::
                                                                    uu____3929
                                                                     in
                                                                    uu____3891
                                                                    ::
                                                                    uu____3904
                                                                     in
                                                                    uu____3866
                                                                    ::
                                                                    uu____3879
                                                                     in
                                                                    uu____3841
                                                                    ::
                                                                    uu____3854
                                                                     in
                                                                    uu____3816
                                                                    ::
                                                                    uu____3829
                                                                     in
                                                                    uu____3791
                                                                    ::
                                                                    uu____3804
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3779
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3767
                                                                     in
                                                                    uu____3742
                                                                    ::
                                                                    uu____3755
                                                                     in
                                                                    uu____3717
                                                                    ::
                                                                    uu____3730
                                                                     in
                                                                    uu____3692
                                                                    ::
                                                                    uu____3705
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3680
                                                                     in
                                                                    uu____3655
                                                                    ::
                                                                    uu____3668
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3643
                                                                     in
                                                                    uu____3618
                                                                    ::
                                                                    uu____3631
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3606
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3594
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3582
                                                                     in
                                                                    uu____3557
                                                                    ::
                                                                    uu____3570
                                                                     in
                                                                    uu____3532
                                                                    ::
                                                                    uu____3545
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (
                                                                    ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3520
                                                                   in
                                                                uu____3495 ::
                                                                  uu____3508
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_ifuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                :: uu____3483
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "initial_fuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of recursive functions to try initially (default 2)")
                                                              :: uu____3471
                                                             in
                                                          uu____3446 ::
                                                            uu____3459
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "include",
                                                          (ReverseAccumulated
                                                             (PathStr "path")),
                                                          "A directory in which to search for files included on the command line")
                                                          :: uu____3434
                                                         in
                                                      uu____3409 ::
                                                        uu____3422
                                                       in
                                                    uu____3384 :: uu____3397
                                                     in
                                                  uu____3359 :: uu____3372
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "hint_file",
                                                  (PathStr "path"),
                                                  "Read/write hints to <path> (instead of module-specific hints files)")
                                                  :: uu____3347
                                                 in
                                              uu____3322 :: uu____3335  in
                                            uu____3297 :: uu____3310  in
                                          (FStar_Getopt.noshort,
                                            "extract_namespace",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr
                                                       "namespace name")))),
                                            "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                            :: uu____3285
                                           in
                                        (FStar_Getopt.noshort,
                                          "extract_module",
                                          (Accumulated
                                             (PostProcessed
                                                (pp_lowercase,
                                                  (SimpleStr "module_name")))),
                                          "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                          :: uu____3273
                                         in
                                      (FStar_Getopt.noshort, "extract",
                                        (Accumulated
                                           (SimpleStr
                                              "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                        "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                        :: uu____3261
                                       in
                                    uu____3236 :: uu____3249  in
                                  uu____3211 :: uu____3224  in
                                (FStar_Getopt.noshort, "dump_module",
                                  (Accumulated (SimpleStr "module_name")),
                                  "") :: uu____3199
                                 in
                              uu____3174 :: uu____3187  in
                            uu____3149 :: uu____3162  in
                          uu____3124 :: uu____3137  in
                        (FStar_Getopt.noshort, "dep",
                          (EnumStr ["make"; "graph"; "full"]),
                          "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                          :: uu____3112
                         in
                      (FStar_Getopt.noshort, "defensive",
                        (EnumStr ["no"; "warn"; "fail"]),
                        "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                        :: uu____3100
                       in
                    (FStar_Getopt.noshort, "debug_level",
                      (Accumulated
                         (OpenEnumStr
                            (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                      "Control the verbosity of debugging info") ::
                      uu____3088
                     in
                  (FStar_Getopt.noshort, "debug",
                    (Accumulated (SimpleStr "module_name")),
                    "Print lots of debugging information while checking module")
                    :: uu____3076
                   in
                (FStar_Getopt.noshort, "codegen-lib",
                  (Accumulated (SimpleStr "namespace")),
                  "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                  :: uu____3064
                 in
              (FStar_Getopt.noshort, "codegen",
                (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                "Generate code for further compilation to executable code, or build a compiler plugin")
                :: uu____3052
               in
            uu____3027 :: uu____3040  in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____3015
           in
        uu____2990 :: uu____3003  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2978
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2966

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5616  ->
    let uu____5619 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5646  ->
         match uu____5646 with
         | (short,long,typ,doc) ->
             let uu____5662 =
               let uu____5674 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5674, doc)  in
             mk_spec uu____5662) uu____5619

let (settable : Prims.string -> Prims.bool) =
  fun uu___81_5684  ->
    match uu___81_5684 with
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
    | "__temp_fast_implicits" -> true
    | "__temp_no_proj" -> true
    | "reuse_hint_for" -> true
    | "warn_error" -> true
    | "z3rlimit_factor" -> true
    | "z3rlimit" -> true
    | "z3refresh" -> true
    | "use_two_phase_tc" -> true
    | "vcgen.optimize_bind_as_seq" -> true
    | uu____5685 -> false
  
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
       (fun uu____5759  ->
          match uu____5759 with
          | (uu____5771,x,uu____5773,uu____5774) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5836  ->
          match uu____5836 with
          | (uu____5848,x,uu____5850,uu____5851) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5862  ->
    let uu____5863 = specs ()  in display_usage_aux uu____5863
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5887 -> true
    | uu____5888 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5895 -> uu____5895
  
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
          let uu____5923 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5923
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5951  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5956 =
             let uu____5959 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5959 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5956)
       in
    let uu____6016 =
      let uu____6019 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6019
       in
    (res, uu____6016)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6057  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6096 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6096 (fun x  -> ())  in
     (let uu____6102 =
        let uu____6107 =
          let uu____6108 = FStar_List.map mk_string old_verify_module  in
          List uu____6108  in
        ("verify_module", uu____6107)  in
      set_option' uu____6102);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6118 =
        let uu____6119 =
          let uu____6120 =
            let uu____6121 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6121  in
          (FStar_String.length f1) - uu____6120  in
        uu____6119 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6118  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6127 = get_lax ()  in
    if uu____6127
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6137 = module_name_of_file_name fn  in should_verify uu____6137
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6143 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6143
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6151 = should_verify m  in
    if uu____6151 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6159  ->
    let uu____6160 = get_no_default_includes ()  in
    if uu____6160
    then get_include ()
    else
      (let lib_paths =
         let uu____6167 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6167 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6176 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6176
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6190 =
         let uu____6193 = get_include ()  in
         FStar_List.append uu____6193 ["."]  in
       FStar_List.append lib_paths uu____6190)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____6206 = FStar_Util.smap_try_find file_map filename  in
    match uu____6206 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            let uu____6222 = FStar_Util.is_path_absolute filename  in
            if uu____6222
            then
              (if FStar_Util.file_exists filename
               then FStar_Pervasives_Native.Some filename
               else FStar_Pervasives_Native.None)
            else
              (let uu____6229 =
                 let uu____6232 = include_path ()  in
                 FStar_List.rev uu____6232  in
               FStar_Util.find_map uu____6229
                 (fun p  ->
                    let path =
                      if p = "."
                      then filename
                      else FStar_Util.join_paths p filename  in
                    if FStar_Util.file_exists path
                    then FStar_Pervasives_Native.Some path
                    else FStar_Pervasives_Native.None))
          with | uu____6248 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____6257  ->
    let uu____6258 = get_prims ()  in
    match uu____6258 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6262 = find_file filename  in
        (match uu____6262 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6266 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6266)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6272  ->
    let uu____6273 = prims ()  in FStar_Util.basename uu____6273
  
let (pervasives : unit -> Prims.string) =
  fun uu____6278  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____6280 = find_file filename  in
    match uu____6280 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____6284 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6284
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6289  ->
    let uu____6290 = pervasives ()  in FStar_Util.basename uu____6290
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6295  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____6297 = find_file filename  in
    match uu____6297 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____6301 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6301
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____6307 = get_odir ()  in
    match uu____6307 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____6316 = get_cache_dir ()  in
    match uu____6316 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6320 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____6320
  
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
             let uu____6386 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____6386  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____6394 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6394 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6464 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6464 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6473  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6478  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6485  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6490  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____6495  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6501 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6507 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6513 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6519 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6526  ->
    let uu____6527 = get_codegen ()  in
    FStar_Util.map_opt uu____6527
      (fun uu___82_6531  ->
         match uu___82_6531 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6532 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6541  ->
    let uu____6542 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6542
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6559  -> let uu____6560 = get_debug ()  in uu____6560 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6570 = get_debug ()  in
    FStar_All.pipe_right uu____6570 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6587 = get_debug ()  in
       FStar_All.pipe_right uu____6587 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6596  -> let uu____6597 = get_defensive ()  in uu____6597 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6602  ->
    let uu____6603 = get_defensive ()  in uu____6603 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6610  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6615  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6620  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6625  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6631 = get_dump_module ()  in
    FStar_All.pipe_right uu____6631 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6640  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6645  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6651 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6651
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6685  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6690  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6695  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6702  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6707  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6712  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6717  ->
    let uu____6718 = get_initial_fuel ()  in
    let uu____6719 = get_max_fuel ()  in Prims.min uu____6718 uu____6719
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6724  ->
    let uu____6725 = get_initial_ifuel ()  in
    let uu____6726 = get_max_ifuel ()  in Prims.min uu____6725 uu____6726
  
let (interactive : unit -> Prims.bool) =
  fun uu____6731  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6736  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6743  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6748  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6753  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6758  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6763  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6768  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6773  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6778  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6783  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6788  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6793  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6800 = get_no_extract ()  in
    FStar_All.pipe_right uu____6800
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6811  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6816  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6821  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6828  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6833  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6838  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6843  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6848  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6853  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6858  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6863  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____6868  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____6873  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6880  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____6885  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6890  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6895  ->
    let uu____6896 = get_smtencoding_nl_arith_repr ()  in
    uu____6896 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6901  ->
    let uu____6902 = get_smtencoding_nl_arith_repr ()  in
    uu____6902 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6907  ->
    let uu____6908 = get_smtencoding_nl_arith_repr ()  in
    uu____6908 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6913  ->
    let uu____6914 = get_smtencoding_l_arith_repr ()  in
    uu____6914 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6919  ->
    let uu____6920 = get_smtencoding_l_arith_repr ()  in
    uu____6920 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6925  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6930  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6935  -> get_tactic_trace_d () 
let (timing : unit -> Prims.bool) = fun uu____6940  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____6945  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____6950  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____6955  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____6960  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____6965  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____6970  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6977  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____6982  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____6995  ->
    let uu____6996 = get_using_facts_from ()  in
    match uu____6996 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7034  ->
    let uu____7035 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____7035
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7042  ->
    let uu____7043 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____7043 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7046 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7053  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____7058  ->
    let uu____7059 = get_smt ()  in
    match uu____7059 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7069  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____7074  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____7079  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7084  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____7089  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7094  ->
    (get_use_two_phase_tc ()) &&
      (let uu____7096 = lax ()  in Prims.op_Negation uu____7096)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7101  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7106  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7111  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7116  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7123 = get_extract ()  in
    match uu____7123 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7134 =
            let uu____7147 = get_no_extract ()  in
            let uu____7150 = get_extract_namespace ()  in
            let uu____7153 = get_extract_module ()  in
            (uu____7147, uu____7150, uu____7153)  in
          match uu____7134 with
          | ([],[],[]) -> ()
          | uu____7168 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7216,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7235 -> false  in
          let uu____7244 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7278  ->
                    match uu____7278 with
                    | (path,uu____7286) -> matches_path m_components path))
             in
          match uu____7244 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____7297,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____7317 = get_extract_namespace ()  in
          match uu____7317 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____7333 = get_extract_module ()  in
          match uu____7333 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____7345 = no_extract m1  in Prims.op_Negation uu____7345) &&
          (let uu____7347 =
             let uu____7356 = get_extract_namespace ()  in
             let uu____7359 = get_extract_module ()  in
             (uu____7356, uu____7359)  in
           (match uu____7347 with
            | ([],[]) -> true
            | uu____7370 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  