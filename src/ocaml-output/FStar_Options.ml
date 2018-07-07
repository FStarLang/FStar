open Prims
let (debug_embedding : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (eager_embedding : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
type debug_level_t =
  | Low 
  | Medium 
  | High 
  | Extreme 
  | Other of Prims.string 
let (uu___is_Low : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | Low  -> true | uu____59 -> false 
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____65 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | High  -> true | uu____71 -> false 
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____77 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____84 -> false
  
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
    match projectee with | Bool _0 -> true | uu____125 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____139 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____153 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____167 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____183 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____202 -> false
  
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
  fun projectee  -> match projectee with | Set  -> true | uu____230 -> false 
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____236 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____242 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____260  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____284  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____308  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___76_332  ->
    match uu___76_332 with
    | Bool b -> b
    | uu____334 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___77_339  ->
    match uu___77_339 with
    | Int b -> b
    | uu____341 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___78_346  ->
    match uu___78_346 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____349 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___79_356  ->
    match uu___79_356 with
    | List ts -> ts
    | uu____362 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____371 .
    (option_val -> 'Auu____371) -> option_val -> 'Auu____371 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____389 = as_list' x  in
      FStar_All.pipe_right uu____389 (FStar_List.map as_t)
  
let as_option :
  'Auu____402 .
    (option_val -> 'Auu____402) ->
      option_val -> 'Auu____402 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___80_417  ->
      match uu___80_417 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____421 = as_t v1  in FStar_Pervasives_Native.Some uu____421
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___81_428  ->
    match uu___81_428 with
    | List ls ->
        let uu____434 =
          FStar_List.map
            (fun l  ->
               let uu____444 = as_string l  in FStar_Util.split uu____444 ",")
            ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____434
    | uu____451 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let (fstar_options : optionstate Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : unit -> optionstate) =
  fun uu____477  ->
    let uu____478 = FStar_ST.op_Bang fstar_options  in
    FStar_List.hd uu____478
  
let (pop : unit -> unit) =
  fun uu____508  ->
    let uu____509 = FStar_ST.op_Bang fstar_options  in
    match uu____509 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____535::[] -> failwith "TOO MANY POPS!"
    | uu____536::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____567  ->
    let uu____568 =
      let uu____571 =
        let uu____572 = peek ()  in FStar_Util.smap_copy uu____572  in
      let uu____575 = FStar_ST.op_Bang fstar_options  in uu____571 ::
        uu____575
       in
    FStar_ST.op_Colon_Equals fstar_options uu____568
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____629 = FStar_ST.op_Bang fstar_options  in
    match uu____629 with
    | [] -> failwith "set on empty option stack"
    | uu____655::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
  
let (snapshot : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____690  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  -> let uu____710 = peek ()  in FStar_Util.smap_add uu____710 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____721  -> match uu____721 with | (k,v1) -> set_option k v1 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    push ();
    (try
       (fun uu___87_747  ->
          match () with | () -> let retv = f ()  in (pop (); retv)) ()
     with | uu___86_752 -> (pop (); FStar_Exn.raise uu___86_752))
  
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____776 =
      let uu____779 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____779
       in
    FStar_ST.op_Colon_Equals light_off_files uu____776
  
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
  ("no_plugins", (Bool false));
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
  ("tactics_failhard", (Bool false));
  ("tactic_raw_binders", (Bool false));
  ("tactic_trace", (Bool false));
  ("tactic_trace_d", (Int (Prims.parse_int "0")));
  ("tcnorm", (Bool true));
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
  fun uu____1242  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1259  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1316 =
      let uu____1319 = peek ()  in FStar_Util.smap_try_find uu____1319 s  in
    match uu____1316 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1329 . Prims.string -> (option_val -> 'Auu____1329) -> 'Auu____1329
  = fun s  -> fun c  -> let uu____1345 = get_option s  in c uu____1345 
let (get_abort_on : unit -> Prims.int) =
  fun uu____1350  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1355  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1362  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1369  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1376  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1383  -> lookup_opt "cache_off" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1390  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1399  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1408  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1417  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____1424  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1431  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1438  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1443  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1448  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1455  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1462  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1467  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1476  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1489  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1498  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1505  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1510  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1515  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1522  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1529  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1534  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1541  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1548  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1553  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1558  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1563  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1570  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1577  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1582  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1587  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1592  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1597  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1602  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1607  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1612  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1619  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1626  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____1631  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1636  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1641  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1648  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1655  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1662  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1669  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1674  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1679  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1684  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1689  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1694  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1699  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1704  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1709  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1716  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1723  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1730  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1737  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1742  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1747  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1752  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____1757  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1762  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1767  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____1772  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____1777  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____1782  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1787  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1792  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1797  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1802  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1807  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1812  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1819  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1826  ->
    let uu____1827 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1827
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1836  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1849  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1858  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1867  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1874  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1879  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1886  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1893  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1898  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1903  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1908  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1913  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1918  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1923  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1928  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1933  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___82_1938  ->
    match uu___82_1938 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1950 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1956 = get_debug_level ()  in
    FStar_All.pipe_right uu____1956
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2089  ->
    let uu____2090 =
      let uu____2091 = FStar_ST.op_Bang _version  in
      let uu____2111 = FStar_ST.op_Bang _platform  in
      let uu____2131 = FStar_ST.op_Bang _compiler  in
      let uu____2151 = FStar_ST.op_Bang _date  in
      let uu____2171 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2091
        uu____2111 uu____2131 uu____2151 uu____2171
       in
    FStar_Util.print_string uu____2090
  
let display_usage_aux :
  'Auu____2197 'Auu____2198 .
    ('Auu____2197,Prims.string,'Auu____2198 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2246  ->
         match uu____2246 with
         | (uu____2257,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2269 =
                      let uu____2270 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2270  in
                    FStar_Util.print_string uu____2269
                  else
                    (let uu____2272 =
                       let uu____2273 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2273 doc  in
                     FStar_Util.print_string uu____2272)
              | FStar_Getopt.OneArg (uu____2274,argname) ->
                  if doc = ""
                  then
                    let uu____2282 =
                      let uu____2283 = FStar_Util.colorize_bold flag  in
                      let uu____2284 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2283 uu____2284
                       in
                    FStar_Util.print_string uu____2282
                  else
                    (let uu____2286 =
                       let uu____2287 = FStar_Util.colorize_bold flag  in
                       let uu____2288 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2287
                         uu____2288 doc
                        in
                     FStar_Util.print_string uu____2286))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2316 = o  in
    match uu____2316 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2352 =
                let uu____2353 = f ()  in set_option name uu____2353  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2368 = f x  in set_option name uu____2368
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2388 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2388  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2411 =
        let uu____2414 = lookup_opt name as_list'  in
        FStar_List.append uu____2414 [value]  in
      mk_list uu____2411
  
let accumulate_string :
  'Auu____2427 .
    Prims.string -> ('Auu____2427 -> Prims.string) -> 'Auu____2427 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2448 =
          let uu____2449 =
            let uu____2450 = post_processor value  in mk_string uu____2450
             in
          accumulated_option name uu____2449  in
        set_option name uu____2448
  
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
    match projectee with | Const _0 -> true | uu____2546 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2560 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2573 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2580 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2594 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2610 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2636 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2675 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2710 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2724 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2745 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2783 -> true
    | uu____2784 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2791 -> uu____2791
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___89_2809  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____2811 ->
                      let uu____2812 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____2812 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____2816 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____2816
                  | PathStr uu____2819 -> mk_path str_val
                  | SimpleStr uu____2820 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____2825 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____2840 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____2840
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
            let uu____2859 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2859
  
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
    | PostProcessed (uu____2896,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2906,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2933 = desc_of_opt_type typ  in
      match uu____2933 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2939  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2956 =
      let uu____2957 = as_string s  in FStar_String.lowercase uu____2957  in
    mk_string uu____2956
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____3005  ->
    let uu____3017 =
      let uu____3029 =
        let uu____3041 =
          let uu____3053 =
            let uu____3063 =
              let uu____3064 = mk_bool true  in Const uu____3064  in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____3063,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
             in
          let uu____3066 =
            let uu____3078 =
              let uu____3090 =
                let uu____3100 =
                  let uu____3101 = mk_bool true  in Const uu____3101  in
                (FStar_Getopt.noshort, "cache_off", uu____3100,
                  "Do not read or write any .checked files")
                 in
              let uu____3103 =
                let uu____3115 =
                  let uu____3127 =
                    let uu____3139 =
                      let uu____3151 =
                        let uu____3163 =
                          let uu____3175 =
                            let uu____3187 =
                              let uu____3197 =
                                let uu____3198 = mk_bool true  in
                                Const uu____3198  in
                              (FStar_Getopt.noshort, "detail_errors",
                                uu____3197,
                                "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                               in
                            let uu____3200 =
                              let uu____3212 =
                                let uu____3222 =
                                  let uu____3223 = mk_bool true  in
                                  Const uu____3223  in
                                (FStar_Getopt.noshort, "detail_hint_replay",
                                  uu____3222,
                                  "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                 in
                              let uu____3225 =
                                let uu____3237 =
                                  let uu____3247 =
                                    let uu____3248 = mk_bool true  in
                                    Const uu____3248  in
                                  (FStar_Getopt.noshort, "doc", uu____3247,
                                    "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                   in
                                let uu____3250 =
                                  let uu____3262 =
                                    let uu____3274 =
                                      let uu____3284 =
                                        let uu____3285 = mk_bool true  in
                                        Const uu____3285  in
                                      (FStar_Getopt.noshort,
                                        "eager_inference", uu____3284,
                                        "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                       in
                                    let uu____3287 =
                                      let uu____3299 =
                                        let uu____3309 =
                                          let uu____3310 = mk_bool true  in
                                          Const uu____3310  in
                                        (FStar_Getopt.noshort,
                                          "eager_subtyping", uu____3309,
                                          "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                         in
                                      let uu____3312 =
                                        let uu____3324 =
                                          let uu____3336 =
                                            let uu____3348 =
                                              let uu____3360 =
                                                let uu____3370 =
                                                  let uu____3371 =
                                                    mk_bool true  in
                                                  Const uu____3371  in
                                                (FStar_Getopt.noshort,
                                                  "expose_interfaces",
                                                  uu____3370,
                                                  "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                 in
                                              let uu____3373 =
                                                let uu____3385 =
                                                  let uu____3395 =
                                                    let uu____3396 =
                                                      mk_bool true  in
                                                    Const uu____3396  in
                                                  (FStar_Getopt.noshort,
                                                    "hide_uvar_nums",
                                                    uu____3395,
                                                    "Don't print unification variable numbers")
                                                   in
                                                let uu____3398 =
                                                  let uu____3410 =
                                                    let uu____3422 =
                                                      let uu____3432 =
                                                        let uu____3433 =
                                                          mk_bool true  in
                                                        Const uu____3433  in
                                                      (FStar_Getopt.noshort,
                                                        "hint_info",
                                                        uu____3432,
                                                        "Print information regarding hints (deprecated; use --query_stats instead)")
                                                       in
                                                    let uu____3435 =
                                                      let uu____3447 =
                                                        let uu____3457 =
                                                          let uu____3458 =
                                                            mk_bool true  in
                                                          Const uu____3458
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "in", uu____3457,
                                                          "Legacy interactive mode; reads input from stdin")
                                                         in
                                                      let uu____3460 =
                                                        let uu____3472 =
                                                          let uu____3482 =
                                                            let uu____3483 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3483
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "ide",
                                                            uu____3482,
                                                            "JSON-based interactive mode for IDEs")
                                                           in
                                                        let uu____3485 =
                                                          let uu____3497 =
                                                            let uu____3509 =
                                                              let uu____3519
                                                                =
                                                                let uu____3520
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____3520
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "indent",
                                                                uu____3519,
                                                                "Parses and outputs the files on the command line")
                                                               in
                                                            let uu____3522 =
                                                              let uu____3534
                                                                =
                                                                let uu____3546
                                                                  =
                                                                  let uu____3558
                                                                    =
                                                                    let uu____3568
                                                                    =
                                                                    let uu____3569
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3569
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3568,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                  let uu____3571
                                                                    =
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
                                                                    "log_types",
                                                                    uu____3605,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3608
                                                                    =
                                                                    let uu____3620
                                                                    =
                                                                    let uu____3630
                                                                    =
                                                                    let uu____3631
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3631
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3630,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3633
                                                                    =
                                                                    let uu____3645
                                                                    =
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
                                                                    "MLish",
                                                                    uu____3691,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3694
                                                                    =
                                                                    let uu____3706
                                                                    =
                                                                    let uu____3718
                                                                    =
                                                                    let uu____3728
                                                                    =
                                                                    let uu____3729
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3729
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3728,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3731
                                                                    =
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
                                                                    "no_location_info",
                                                                    uu____3765,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
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
                                                                    "no_smt",
                                                                    uu____3790,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
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
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3815,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3818
                                                                    =
                                                                    let uu____3830
                                                                    =
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
                                                                    "print_bound_var_types",
                                                                    uu____3864,
                                                                    "Print the types of bound variables")
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
                                                                    "print_effect_args",
                                                                    uu____3889,
                                                                    "Print inferred predicate transformers for all computation types")
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
                                                                    "print_full_names",
                                                                    uu____3914,
                                                                    "Print full names of variables")
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
                                                                    "print_implicits",
                                                                    uu____3939,
                                                                    "Print implicit arguments")
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
                                                                    "print_universes",
                                                                    uu____3964,
                                                                    "Print universes")
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
                                                                    "print_z3_statistics",
                                                                    uu____3989,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
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
                                                                    "prn",
                                                                    uu____4014,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
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
                                                                    "query_stats",
                                                                    uu____4039,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____4042
                                                                    =
                                                                    let uu____4054
                                                                    =
                                                                    let uu____4064
                                                                    =
                                                                    let uu____4065
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4065
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____4064,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____4067
                                                                    =
                                                                    let uu____4079
                                                                    =
                                                                    let uu____4091
                                                                    =
                                                                    let uu____4101
                                                                    =
                                                                    let uu____4102
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4102
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4101,
                                                                    " ")  in
                                                                    let uu____4104
                                                                    =
                                                                    let uu____4116
                                                                    =
                                                                    let uu____4128
                                                                    =
                                                                    let uu____4140
                                                                    =
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
                                                                    "tactic_raw_binders",
                                                                    uu____4174,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4177
                                                                    =
                                                                    let uu____4189
                                                                    =
                                                                    let uu____4199
                                                                    =
                                                                    let uu____4200
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4200
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____4199,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____4202
                                                                    =
                                                                    let uu____4214
                                                                    =
                                                                    let uu____4224
                                                                    =
                                                                    let uu____4225
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4225
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4224,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4227
                                                                    =
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
                                                                    "__tactics_nbe",
                                                                    uu____4261,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____4264
                                                                    =
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
                                                                    "timing",
                                                                    uu____4298,
                                                                    "Print the time it takes to verify each top-level definition")
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
                                                                    "trace_error",
                                                                    uu____4323,
                                                                    "Don't print an error message; show an exception trace instead")
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
                                                                    "ugly",
                                                                    uu____4348,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4351
                                                                    =
                                                                    let uu____4363
                                                                    =
                                                                    let uu____4373
                                                                    =
                                                                    let uu____4374
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4374
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4373,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4376
                                                                    =
                                                                    let uu____4388
                                                                    =
                                                                    let uu____4398
                                                                    =
                                                                    let uu____4399
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4399
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4398,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4401
                                                                    =
                                                                    let uu____4413
                                                                    =
                                                                    let uu____4423
                                                                    =
                                                                    let uu____4424
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4424
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4423,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
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
                                                                    "use_hints",
                                                                    uu____4448,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4451
                                                                    =
                                                                    let uu____4463
                                                                    =
                                                                    let uu____4473
                                                                    =
                                                                    let uu____4474
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4474
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4473,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4476
                                                                    =
                                                                    let uu____4488
                                                                    =
                                                                    let uu____4500
                                                                    =
                                                                    let uu____4510
                                                                    =
                                                                    let uu____4511
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4511
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____4510,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____4513
                                                                    =
                                                                    let uu____4525
                                                                    =
                                                                    let uu____4535
                                                                    =
                                                                    let uu____4536
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4536
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4535,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4538
                                                                    =
                                                                    let uu____4550
                                                                    =
                                                                    let uu____4562
                                                                    =
                                                                    let uu____4574
                                                                    =
                                                                    let uu____4586
                                                                    =
                                                                    let uu____4596
                                                                    =
                                                                    let uu____4597
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4597
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4596,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4599
                                                                    =
                                                                    let uu____4611
                                                                    =
                                                                    let uu____4621
                                                                    =
                                                                    let uu____4622
                                                                    =
                                                                    let uu____4630
                                                                    =
                                                                    let uu____4631
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4631
                                                                     in
                                                                    ((fun
                                                                    uu____4637
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4630)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4622
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4621,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4641
                                                                    =
                                                                    let uu____4653
                                                                    =
                                                                    let uu____4663
                                                                    =
                                                                    let uu____4664
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4664
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4663,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4666
                                                                    =
                                                                    let uu____4678
                                                                    =
                                                                    let uu____4690
                                                                    =
                                                                    let uu____4700
                                                                    =
                                                                    let uu____4701
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4701
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4700,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4703
                                                                    =
                                                                    let uu____4715
                                                                    =
                                                                    let uu____4727
                                                                    =
                                                                    let uu____4739
                                                                    =
                                                                    let uu____4751
                                                                    =
                                                                    let uu____4763
                                                                    =
                                                                    let uu____4773
                                                                    =
                                                                    let uu____4774
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4774
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4773,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4776
                                                                    =
                                                                    let uu____4788
                                                                    =
                                                                    let uu____4798
                                                                    =
                                                                    let uu____4799
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4799
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4798,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4801
                                                                    =
                                                                    let uu____4813
                                                                    =
                                                                    let uu____4825
                                                                    =
                                                                    let uu____4837
                                                                    =
                                                                    let uu____4847
                                                                    =
                                                                    let uu____4848
                                                                    =
                                                                    let uu____4856
                                                                    =
                                                                    let uu____4857
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4857
                                                                     in
                                                                    ((fun
                                                                    uu____4862
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____4856)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4848
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____4847,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____4883
                                                                    =
                                                                    let uu____4895
                                                                    =
                                                                    let uu____4905
                                                                    =
                                                                    let uu____4906
                                                                    =
                                                                    let uu____4914
                                                                    =
                                                                    let uu____4915
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4915
                                                                     in
                                                                    ((fun
                                                                    uu____4920
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____4914)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4906
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____4905,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____4941
                                                                    =
                                                                    let uu____4953
                                                                    =
                                                                    let uu____4963
                                                                    =
                                                                    let uu____4964
                                                                    =
                                                                    let uu____4972
                                                                    =
                                                                    let uu____4973
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4973
                                                                     in
                                                                    ((fun
                                                                    uu____4979
                                                                     ->
                                                                    (
                                                                    let uu____4981
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4981);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4972)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4964
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4963,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4953]
                                                                     in
                                                                    uu____4895
                                                                    ::
                                                                    uu____4941
                                                                     in
                                                                    uu____4837
                                                                    ::
                                                                    uu____4883
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4825
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4813
                                                                     in
                                                                    uu____4788
                                                                    ::
                                                                    uu____4801
                                                                     in
                                                                    uu____4763
                                                                    ::
                                                                    uu____4776
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4751
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4739
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4727
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4715
                                                                     in
                                                                    uu____4690
                                                                    ::
                                                                    uu____4703
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4678
                                                                     in
                                                                    uu____4653
                                                                    ::
                                                                    uu____4666
                                                                     in
                                                                    uu____4611
                                                                    ::
                                                                    uu____4641
                                                                     in
                                                                    uu____4586
                                                                    ::
                                                                    uu____4599
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4574
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4562
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4550
                                                                     in
                                                                    uu____4525
                                                                    ::
                                                                    uu____4538
                                                                     in
                                                                    uu____4500
                                                                    ::
                                                                    uu____4513
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4488
                                                                     in
                                                                    uu____4463
                                                                    ::
                                                                    uu____4476
                                                                     in
                                                                    uu____4438
                                                                    ::
                                                                    uu____4451
                                                                     in
                                                                    uu____4413
                                                                    ::
                                                                    uu____4426
                                                                     in
                                                                    uu____4388
                                                                    ::
                                                                    uu____4401
                                                                     in
                                                                    uu____4363
                                                                    ::
                                                                    uu____4376
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
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____4276
                                                                     in
                                                                    uu____4251
                                                                    ::
                                                                    uu____4264
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4239
                                                                     in
                                                                    uu____4214
                                                                    ::
                                                                    uu____4227
                                                                     in
                                                                    uu____4189
                                                                    ::
                                                                    uu____4202
                                                                     in
                                                                    uu____4164
                                                                    ::
                                                                    uu____4177
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4152
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4140
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4128
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4116
                                                                     in
                                                                    uu____4091
                                                                    ::
                                                                    uu____4104
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____4079
                                                                     in
                                                                    uu____4054
                                                                    ::
                                                                    uu____4067
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
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3842
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3830
                                                                     in
                                                                    uu____3805
                                                                    ::
                                                                    uu____3818
                                                                     in
                                                                    uu____3780
                                                                    ::
                                                                    uu____3793
                                                                     in
                                                                    uu____3755
                                                                    ::
                                                                    uu____3768
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3743
                                                                     in
                                                                    uu____3718
                                                                    ::
                                                                    uu____3731
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3706
                                                                     in
                                                                    uu____3681
                                                                    ::
                                                                    uu____3694
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3669
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3657
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3645
                                                                     in
                                                                    uu____3620
                                                                    ::
                                                                    uu____3633
                                                                     in
                                                                    uu____3595
                                                                    ::
                                                                    uu____3608
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3583
                                                                     in
                                                                  uu____3558
                                                                    ::
                                                                    uu____3571
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_ifuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                  ::
                                                                  uu____3546
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_fuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of recursive functions to try initially (default 2)")
                                                                :: uu____3534
                                                               in
                                                            uu____3509 ::
                                                              uu____3522
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "include",
                                                            (ReverseAccumulated
                                                               (PathStr
                                                                  "path")),
                                                            "A directory in which to search for files included on the command line")
                                                            :: uu____3497
                                                           in
                                                        uu____3472 ::
                                                          uu____3485
                                                         in
                                                      uu____3447 ::
                                                        uu____3460
                                                       in
                                                    uu____3422 :: uu____3435
                                                     in
                                                  (FStar_Getopt.noshort,
                                                    "hint_file",
                                                    (PathStr "path"),
                                                    "Read/write hints to <path> (instead of module-specific hints files)")
                                                    :: uu____3410
                                                   in
                                                uu____3385 :: uu____3398  in
                                              uu____3360 :: uu____3373  in
                                            (FStar_Getopt.noshort,
                                              "extract_namespace",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "namespace name")))),
                                              "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                              :: uu____3348
                                             in
                                          (FStar_Getopt.noshort,
                                            "extract_module",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr "module_name")))),
                                            "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                            :: uu____3336
                                           in
                                        (FStar_Getopt.noshort, "extract",
                                          (Accumulated
                                             (SimpleStr
                                                "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                          "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                          :: uu____3324
                                         in
                                      uu____3299 :: uu____3312  in
                                    uu____3274 :: uu____3287  in
                                  (FStar_Getopt.noshort, "dump_module",
                                    (Accumulated (SimpleStr "module_name")),
                                    "") :: uu____3262
                                   in
                                uu____3237 :: uu____3250  in
                              uu____3212 :: uu____3225  in
                            uu____3187 :: uu____3200  in
                          (FStar_Getopt.noshort, "dep",
                            (EnumStr ["make"; "graph"; "full"]),
                            "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                            :: uu____3175
                           in
                        (FStar_Getopt.noshort, "defensive",
                          (EnumStr ["no"; "warn"; "fail"]),
                          "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                          :: uu____3163
                         in
                      (FStar_Getopt.noshort, "debug_level",
                        (Accumulated
                           (OpenEnumStr
                              (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                        "Control the verbosity of debugging info") ::
                        uu____3151
                       in
                    (FStar_Getopt.noshort, "debug",
                      (Accumulated (SimpleStr "module_name")),
                      "Print lots of debugging information while checking module")
                      :: uu____3139
                     in
                  (FStar_Getopt.noshort, "codegen-lib",
                    (Accumulated (SimpleStr "namespace")),
                    "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                    :: uu____3127
                   in
                (FStar_Getopt.noshort, "codegen",
                  (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                  "Generate code for further compilation to executable code, or build a compiler plugin")
                  :: uu____3115
                 in
              uu____3090 :: uu____3103  in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____3078
             in
          uu____3053 :: uu____3066  in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____3041
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____3029
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___83_5953  ->
             match uu___83_5953 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____3017

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5976  ->
    let uu____5979 = specs_with_types ()  in
    FStar_List.map
      (fun uu____6006  ->
         match uu____6006 with
         | (short,long,typ,doc) ->
             let uu____6022 =
               let uu____6034 = arg_spec_of_opt_type long typ  in
               (short, long, uu____6034, doc)  in
             mk_spec uu____6022) uu____5979

let (settable : Prims.string -> Prims.bool) =
  fun uu___84_6044  ->
    match uu___84_6044 with
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
    | "no_plugins" -> true
    | "no_tactics" -> true
    | "normalize_pure_terms_for_extraction" -> true
    | "tactic_raw_binders" -> true
    | "tactics_failhard" -> true
    | "tactic_trace" -> true
    | "tactic_trace_d" -> true
    | "tcnorm" -> true
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
    | uu____6045 -> false
  
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
       (fun uu____6119  ->
          match uu____6119 with
          | (uu____6131,x,uu____6133,uu____6134) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____6196  ->
          match uu____6196 with
          | (uu____6208,x,uu____6210,uu____6211) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____6222  ->
    let uu____6223 = specs ()  in display_usage_aux uu____6223
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____6247 -> true
    | uu____6248 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____6255 -> uu____6255
  
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
        (fun uu___91_6272  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____6283 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____6283
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____6311  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____6316 =
             let uu____6319 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____6319 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____6316)
       in
    let uu____6368 =
      let uu____6371 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6371
       in
    (res, uu____6368)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6405  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6440 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6440 (fun x  -> ())  in
     (let uu____6446 =
        let uu____6451 =
          let uu____6452 = FStar_List.map mk_string old_verify_module  in
          List uu____6452  in
        ("verify_module", uu____6451)  in
      set_option' uu____6446);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6462 =
        let uu____6463 =
          let uu____6464 =
            let uu____6465 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6465  in
          (FStar_String.length f1) - uu____6464  in
        uu____6463 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6462  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6471 = get_lax ()  in
    if uu____6471
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6481 = module_name_of_file_name fn  in should_verify uu____6481
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6487 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6487
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6495 = should_verify m  in
    if uu____6495 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6503  ->
    let uu____6504 = get_no_default_includes ()  in
    if uu____6504
    then get_include ()
    else
      (let lib_paths =
         let uu____6511 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6511 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6520 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6520
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6534 =
         let uu____6537 = get_include ()  in
         FStar_List.append uu____6537 ["."]  in
       FStar_List.append lib_paths uu____6534)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____6550 = FStar_Util.smap_try_find file_map filename  in
    match uu____6550 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___93_6563  ->
               match () with
               | () ->
                   let uu____6566 = FStar_Util.is_path_absolute filename  in
                   if uu____6566
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____6573 =
                        let uu____6576 = include_path ()  in
                        FStar_List.rev uu____6576  in
                      FStar_Util.find_map uu____6573
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___92_6588 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____6599  ->
    let uu____6600 = get_prims ()  in
    match uu____6600 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6604 = find_file filename  in
        (match uu____6604 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6608 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6608)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6614  ->
    let uu____6615 = prims ()  in FStar_Util.basename uu____6615
  
let (pervasives : unit -> Prims.string) =
  fun uu____6620  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____6622 = find_file filename  in
    match uu____6622 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____6626 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6626
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6631  ->
    let uu____6632 = pervasives ()  in FStar_Util.basename uu____6632
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6637  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____6639 = find_file filename  in
    match uu____6639 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____6643 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6643
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____6649 = get_odir ()  in
    match uu____6649 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____6658 = get_cache_dir ()  in
    match uu____6658 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6662 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____6662
  
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
             let uu____6728 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____6728  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____6736 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6736 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6806 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6806 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6815  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6820  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6827  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6832  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____6837  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6843 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6849 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6855 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6861 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6868  ->
    let uu____6869 = get_codegen ()  in
    FStar_Util.map_opt uu____6869
      (fun uu___85_6873  ->
         match uu___85_6873 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6874 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6883  ->
    let uu____6884 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6884
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6901  -> let uu____6902 = get_debug ()  in uu____6902 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6912 = get_debug ()  in
    FStar_All.pipe_right uu____6912 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6929 = get_debug ()  in
       FStar_All.pipe_right uu____6929 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6938  -> let uu____6939 = get_defensive ()  in uu____6939 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6944  ->
    let uu____6945 = get_defensive ()  in uu____6945 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6952  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6957  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6962  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6967  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6973 = get_dump_module ()  in
    FStar_All.pipe_right uu____6973 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6982  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6987  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6993 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6993
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____7023  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____7028  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____7033  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7040  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____7045  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____7050  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____7055  ->
    let uu____7056 = get_initial_fuel ()  in
    let uu____7057 = get_max_fuel ()  in Prims.min uu____7056 uu____7057
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____7062  ->
    let uu____7063 = get_initial_ifuel ()  in
    let uu____7064 = get_max_ifuel ()  in Prims.min uu____7063 uu____7064
  
let (interactive : unit -> Prims.bool) =
  fun uu____7069  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____7074  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____7081  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____7086  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____7091  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____7096  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____7101  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____7106  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____7111  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____7116  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____7121  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____7126  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____7131  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____7138 = get_no_extract ()  in
    FStar_All.pipe_right uu____7138
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____7149  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____7154  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____7159  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____7164  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7171  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____7176  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____7181  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____7186  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____7191  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____7196  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____7201  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____7206  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____7211  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____7216  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7223  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____7228  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____7233  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____7238  ->
    let uu____7239 = get_smtencoding_nl_arith_repr ()  in
    uu____7239 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____7244  ->
    let uu____7245 = get_smtencoding_nl_arith_repr ()  in
    uu____7245 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____7250  ->
    let uu____7251 = get_smtencoding_nl_arith_repr ()  in
    uu____7251 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____7256  ->
    let uu____7257 = get_smtencoding_l_arith_repr ()  in
    uu____7257 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____7262  ->
    let uu____7263 = get_smtencoding_l_arith_repr ()  in
    uu____7263 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____7268  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____7273  -> get_tactics_failhard () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____7278  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____7283  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____7288  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____7293  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____7298  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____7303  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____7308  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____7313  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____7318  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____7323  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____7328  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7335  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____7340  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____7353  ->
    let uu____7354 = get_using_facts_from ()  in
    match uu____7354 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7392  ->
    let uu____7393 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____7393
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7400  ->
    let uu____7401 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____7401 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7404 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7411  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____7416  ->
    let uu____7417 = get_smt ()  in
    match uu____7417 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7427  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____7432  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____7437  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7442  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____7447  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7452  ->
    (get_use_two_phase_tc ()) &&
      (let uu____7454 = lax ()  in Prims.op_Negation uu____7454)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7459  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7464  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7469  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7474  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7481 = get_extract ()  in
    match uu____7481 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7492 =
            let uu____7505 = get_no_extract ()  in
            let uu____7508 = get_extract_namespace ()  in
            let uu____7511 = get_extract_module ()  in
            (uu____7505, uu____7508, uu____7511)  in
          match uu____7492 with
          | ([],[],[]) -> ()
          | uu____7526 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7574,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7593 -> false  in
          let uu____7602 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7636  ->
                    match uu____7636 with
                    | (path,uu____7644) -> matches_path m_components path))
             in
          match uu____7602 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____7655,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____7675 = get_extract_namespace ()  in
          match uu____7675 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____7691 = get_extract_module ()  in
          match uu____7691 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____7703 = no_extract m1  in Prims.op_Negation uu____7703) &&
          (let uu____7705 =
             let uu____7714 = get_extract_namespace ()  in
             let uu____7717 = get_extract_module ()  in
             (uu____7714, uu____7717)  in
           (match uu____7705 with
            | ([],[]) -> true
            | uu____7728 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  