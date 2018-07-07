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
  fun uu____1238  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1255  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1312 =
      let uu____1315 = peek ()  in FStar_Util.smap_try_find uu____1315 s  in
    match uu____1312 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1325 . Prims.string -> (option_val -> 'Auu____1325) -> 'Auu____1325
  = fun s  -> fun c  -> let uu____1341 = get_option s  in c uu____1341 
let (get_abort_on : unit -> Prims.int) =
  fun uu____1346  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1351  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1358  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1365  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1372  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1379  -> lookup_opt "cache_off" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1386  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1395  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1404  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1413  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____1420  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1427  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1434  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1439  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1444  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1451  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1458  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1463  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1472  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1485  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1494  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1501  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1506  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1511  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1518  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1525  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1530  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1537  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1544  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1549  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1554  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1559  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1566  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1573  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1578  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1583  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1588  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1593  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1598  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1603  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1608  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1615  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1622  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____1627  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1632  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1637  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1644  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1651  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1658  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1665  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1670  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1675  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1680  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1685  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1690  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1695  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1700  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1705  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1712  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1719  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1726  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1733  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1738  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1743  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1748  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1753  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1758  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____1763  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____1768  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____1773  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1778  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1783  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1788  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1793  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1798  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1803  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1810  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1817  ->
    let uu____1818 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1818
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1827  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1840  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1849  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1858  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1865  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1870  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1877  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1884  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1889  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1894  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1899  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1904  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1909  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1914  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1919  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1924  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___82_1929  ->
    match uu___82_1929 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1941 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1947 = get_debug_level ()  in
    FStar_All.pipe_right uu____1947
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2080  ->
    let uu____2081 =
      let uu____2082 = FStar_ST.op_Bang _version  in
      let uu____2102 = FStar_ST.op_Bang _platform  in
      let uu____2122 = FStar_ST.op_Bang _compiler  in
      let uu____2142 = FStar_ST.op_Bang _date  in
      let uu____2162 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2082
        uu____2102 uu____2122 uu____2142 uu____2162
       in
    FStar_Util.print_string uu____2081
  
let display_usage_aux :
  'Auu____2188 'Auu____2189 .
    ('Auu____2188,Prims.string,'Auu____2189 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2237  ->
         match uu____2237 with
         | (uu____2248,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2260 =
                      let uu____2261 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2261  in
                    FStar_Util.print_string uu____2260
                  else
                    (let uu____2263 =
                       let uu____2264 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2264 doc  in
                     FStar_Util.print_string uu____2263)
              | FStar_Getopt.OneArg (uu____2265,argname) ->
                  if doc = ""
                  then
                    let uu____2273 =
                      let uu____2274 = FStar_Util.colorize_bold flag  in
                      let uu____2275 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2274 uu____2275
                       in
                    FStar_Util.print_string uu____2273
                  else
                    (let uu____2277 =
                       let uu____2278 = FStar_Util.colorize_bold flag  in
                       let uu____2279 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2278
                         uu____2279 doc
                        in
                     FStar_Util.print_string uu____2277))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2307 = o  in
    match uu____2307 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2343 =
                let uu____2344 = f ()  in set_option name uu____2344  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2359 = f x  in set_option name uu____2359
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2379 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2379  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2402 =
        let uu____2405 = lookup_opt name as_list'  in
        FStar_List.append uu____2405 [value]  in
      mk_list uu____2402
  
let accumulate_string :
  'Auu____2418 .
    Prims.string -> ('Auu____2418 -> Prims.string) -> 'Auu____2418 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2439 =
          let uu____2440 =
            let uu____2441 = post_processor value  in mk_string uu____2441
             in
          accumulated_option name uu____2440  in
        set_option name uu____2439
  
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
    match projectee with | Const _0 -> true | uu____2537 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2551 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2564 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2571 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2585 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2601 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2627 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2666 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2701 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2715 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2736 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2774 -> true
    | uu____2775 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2782 -> uu____2782
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___89_2800  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____2802 ->
                      let uu____2803 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____2803 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____2807 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____2807
                  | PathStr uu____2810 -> mk_path str_val
                  | SimpleStr uu____2811 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____2816 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____2831 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____2831
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
            let uu____2850 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2850
  
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
    | PostProcessed (uu____2887,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2897,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2924 = desc_of_opt_type typ  in
      match uu____2924 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2930  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2947 =
      let uu____2948 = as_string s  in FStar_String.lowercase uu____2948  in
    mk_string uu____2947
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2996  ->
    let uu____3008 =
      let uu____3020 =
        let uu____3032 =
          let uu____3044 =
            let uu____3054 =
              let uu____3055 = mk_bool true  in Const uu____3055  in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____3054,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
             in
          let uu____3057 =
            let uu____3069 =
              let uu____3081 =
                let uu____3091 =
                  let uu____3092 = mk_bool true  in Const uu____3092  in
                (FStar_Getopt.noshort, "cache_off", uu____3091,
                  "Do not read or write any .checked files")
                 in
              let uu____3094 =
                let uu____3106 =
                  let uu____3118 =
                    let uu____3130 =
                      let uu____3142 =
                        let uu____3154 =
                          let uu____3166 =
                            let uu____3178 =
                              let uu____3188 =
                                let uu____3189 = mk_bool true  in
                                Const uu____3189  in
                              (FStar_Getopt.noshort, "detail_errors",
                                uu____3188,
                                "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                               in
                            let uu____3191 =
                              let uu____3203 =
                                let uu____3213 =
                                  let uu____3214 = mk_bool true  in
                                  Const uu____3214  in
                                (FStar_Getopt.noshort, "detail_hint_replay",
                                  uu____3213,
                                  "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                 in
                              let uu____3216 =
                                let uu____3228 =
                                  let uu____3238 =
                                    let uu____3239 = mk_bool true  in
                                    Const uu____3239  in
                                  (FStar_Getopt.noshort, "doc", uu____3238,
                                    "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                   in
                                let uu____3241 =
                                  let uu____3253 =
                                    let uu____3265 =
                                      let uu____3275 =
                                        let uu____3276 = mk_bool true  in
                                        Const uu____3276  in
                                      (FStar_Getopt.noshort,
                                        "eager_inference", uu____3275,
                                        "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                       in
                                    let uu____3278 =
                                      let uu____3290 =
                                        let uu____3300 =
                                          let uu____3301 = mk_bool true  in
                                          Const uu____3301  in
                                        (FStar_Getopt.noshort,
                                          "eager_subtyping", uu____3300,
                                          "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                         in
                                      let uu____3303 =
                                        let uu____3315 =
                                          let uu____3327 =
                                            let uu____3339 =
                                              let uu____3351 =
                                                let uu____3361 =
                                                  let uu____3362 =
                                                    mk_bool true  in
                                                  Const uu____3362  in
                                                (FStar_Getopt.noshort,
                                                  "expose_interfaces",
                                                  uu____3361,
                                                  "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                 in
                                              let uu____3364 =
                                                let uu____3376 =
                                                  let uu____3386 =
                                                    let uu____3387 =
                                                      mk_bool true  in
                                                    Const uu____3387  in
                                                  (FStar_Getopt.noshort,
                                                    "hide_uvar_nums",
                                                    uu____3386,
                                                    "Don't print unification variable numbers")
                                                   in
                                                let uu____3389 =
                                                  let uu____3401 =
                                                    let uu____3413 =
                                                      let uu____3423 =
                                                        let uu____3424 =
                                                          mk_bool true  in
                                                        Const uu____3424  in
                                                      (FStar_Getopt.noshort,
                                                        "hint_info",
                                                        uu____3423,
                                                        "Print information regarding hints (deprecated; use --query_stats instead)")
                                                       in
                                                    let uu____3426 =
                                                      let uu____3438 =
                                                        let uu____3448 =
                                                          let uu____3449 =
                                                            mk_bool true  in
                                                          Const uu____3449
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "in", uu____3448,
                                                          "Legacy interactive mode; reads input from stdin")
                                                         in
                                                      let uu____3451 =
                                                        let uu____3463 =
                                                          let uu____3473 =
                                                            let uu____3474 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3474
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "ide",
                                                            uu____3473,
                                                            "JSON-based interactive mode for IDEs")
                                                           in
                                                        let uu____3476 =
                                                          let uu____3488 =
                                                            let uu____3500 =
                                                              let uu____3510
                                                                =
                                                                let uu____3511
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____3511
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "indent",
                                                                uu____3510,
                                                                "Parses and outputs the files on the command line")
                                                               in
                                                            let uu____3513 =
                                                              let uu____3525
                                                                =
                                                                let uu____3537
                                                                  =
                                                                  let uu____3549
                                                                    =
                                                                    let uu____3559
                                                                    =
                                                                    let uu____3560
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3560
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3559,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                  let uu____3562
                                                                    =
                                                                    let uu____3574
                                                                    =
                                                                    let uu____3586
                                                                    =
                                                                    let uu____3596
                                                                    =
                                                                    let uu____3597
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3597
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3596,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3599
                                                                    =
                                                                    let uu____3611
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
                                                                    "log_queries",
                                                                    uu____3621,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3624
                                                                    =
                                                                    let uu____3636
                                                                    =
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
                                                                    "MLish",
                                                                    uu____3682,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3685
                                                                    =
                                                                    let uu____3697
                                                                    =
                                                                    let uu____3709
                                                                    =
                                                                    let uu____3719
                                                                    =
                                                                    let uu____3720
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3720
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3719,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3722
                                                                    =
                                                                    let uu____3734
                                                                    =
                                                                    let uu____3746
                                                                    =
                                                                    let uu____3756
                                                                    =
                                                                    let uu____3757
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3757
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3756,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
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
                                                                    "no_smt",
                                                                    uu____3781,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
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
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3806,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3809
                                                                    =
                                                                    let uu____3821
                                                                    =
                                                                    let uu____3833
                                                                    =
                                                                    let uu____3845
                                                                    =
                                                                    let uu____3855
                                                                    =
                                                                    let uu____3856
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3856
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3855,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3858
                                                                    =
                                                                    let uu____3870
                                                                    =
                                                                    let uu____3880
                                                                    =
                                                                    let uu____3881
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3881
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3880,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3883
                                                                    =
                                                                    let uu____3895
                                                                    =
                                                                    let uu____3905
                                                                    =
                                                                    let uu____3906
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3906
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3905,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3908
                                                                    =
                                                                    let uu____3920
                                                                    =
                                                                    let uu____3930
                                                                    =
                                                                    let uu____3931
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3931
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3930,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3933
                                                                    =
                                                                    let uu____3945
                                                                    =
                                                                    let uu____3955
                                                                    =
                                                                    let uu____3956
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3956
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3955,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3958
                                                                    =
                                                                    let uu____3970
                                                                    =
                                                                    let uu____3980
                                                                    =
                                                                    let uu____3981
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3981
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3980,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3983
                                                                    =
                                                                    let uu____3995
                                                                    =
                                                                    let uu____4005
                                                                    =
                                                                    let uu____4006
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4006
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____4005,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____4008
                                                                    =
                                                                    let uu____4020
                                                                    =
                                                                    let uu____4030
                                                                    =
                                                                    let uu____4031
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4031
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____4030,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____4033
                                                                    =
                                                                    let uu____4045
                                                                    =
                                                                    let uu____4055
                                                                    =
                                                                    let uu____4056
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4056
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____4055,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____4058
                                                                    =
                                                                    let uu____4070
                                                                    =
                                                                    let uu____4082
                                                                    =
                                                                    let uu____4092
                                                                    =
                                                                    let uu____4093
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4093
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4092,
                                                                    " ")  in
                                                                    let uu____4095
                                                                    =
                                                                    let uu____4107
                                                                    =
                                                                    let uu____4119
                                                                    =
                                                                    let uu____4131
                                                                    =
                                                                    let uu____4143
                                                                    =
                                                                    let uu____4155
                                                                    =
                                                                    let uu____4165
                                                                    =
                                                                    let uu____4166
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4166
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4165,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4168
                                                                    =
                                                                    let uu____4180
                                                                    =
                                                                    let uu____4190
                                                                    =
                                                                    let uu____4191
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4191
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4190,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4193
                                                                    =
                                                                    let uu____4205
                                                                    =
                                                                    let uu____4217
                                                                    =
                                                                    let uu____4227
                                                                    =
                                                                    let uu____4228
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4228
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____4227,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____4230
                                                                    =
                                                                    let uu____4242
                                                                    =
                                                                    let uu____4254
                                                                    =
                                                                    let uu____4264
                                                                    =
                                                                    let uu____4265
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4265
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4264,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4267
                                                                    =
                                                                    let uu____4279
                                                                    =
                                                                    let uu____4289
                                                                    =
                                                                    let uu____4290
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4290
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4289,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4292
                                                                    =
                                                                    let uu____4304
                                                                    =
                                                                    let uu____4314
                                                                    =
                                                                    let uu____4315
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4315
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4314,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4317
                                                                    =
                                                                    let uu____4329
                                                                    =
                                                                    let uu____4339
                                                                    =
                                                                    let uu____4340
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4340
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4339,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4342
                                                                    =
                                                                    let uu____4354
                                                                    =
                                                                    let uu____4364
                                                                    =
                                                                    let uu____4365
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4365
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4364,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4367
                                                                    =
                                                                    let uu____4379
                                                                    =
                                                                    let uu____4389
                                                                    =
                                                                    let uu____4390
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4390
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4389,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4392
                                                                    =
                                                                    let uu____4404
                                                                    =
                                                                    let uu____4414
                                                                    =
                                                                    let uu____4415
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4415
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4414,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4417
                                                                    =
                                                                    let uu____4429
                                                                    =
                                                                    let uu____4439
                                                                    =
                                                                    let uu____4440
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4440
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4439,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4442
                                                                    =
                                                                    let uu____4454
                                                                    =
                                                                    let uu____4466
                                                                    =
                                                                    let uu____4476
                                                                    =
                                                                    let uu____4477
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4477
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____4476,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____4479
                                                                    =
                                                                    let uu____4491
                                                                    =
                                                                    let uu____4501
                                                                    =
                                                                    let uu____4502
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4502
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4501,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4504
                                                                    =
                                                                    let uu____4516
                                                                    =
                                                                    let uu____4528
                                                                    =
                                                                    let uu____4540
                                                                    =
                                                                    let uu____4552
                                                                    =
                                                                    let uu____4562
                                                                    =
                                                                    let uu____4563
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4563
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4562,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4565
                                                                    =
                                                                    let uu____4577
                                                                    =
                                                                    let uu____4587
                                                                    =
                                                                    let uu____4588
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
                                                                    ((fun
                                                                    uu____4603
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4596)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4588
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4587,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4607
                                                                    =
                                                                    let uu____4619
                                                                    =
                                                                    let uu____4629
                                                                    =
                                                                    let uu____4630
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4630
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4629,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4632
                                                                    =
                                                                    let uu____4644
                                                                    =
                                                                    let uu____4656
                                                                    =
                                                                    let uu____4666
                                                                    =
                                                                    let uu____4667
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4667
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4666,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4669
                                                                    =
                                                                    let uu____4681
                                                                    =
                                                                    let uu____4693
                                                                    =
                                                                    let uu____4705
                                                                    =
                                                                    let uu____4717
                                                                    =
                                                                    let uu____4729
                                                                    =
                                                                    let uu____4739
                                                                    =
                                                                    let uu____4740
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4740
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4739,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4742
                                                                    =
                                                                    let uu____4754
                                                                    =
                                                                    let uu____4764
                                                                    =
                                                                    let uu____4765
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4765
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4764,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4767
                                                                    =
                                                                    let uu____4779
                                                                    =
                                                                    let uu____4791
                                                                    =
                                                                    let uu____4803
                                                                    =
                                                                    let uu____4813
                                                                    =
                                                                    let uu____4814
                                                                    =
                                                                    let uu____4822
                                                                    =
                                                                    let uu____4823
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4823
                                                                     in
                                                                    ((fun
                                                                    uu____4828
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____4822)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4814
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____4813,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____4849
                                                                    =
                                                                    let uu____4861
                                                                    =
                                                                    let uu____4871
                                                                    =
                                                                    let uu____4872
                                                                    =
                                                                    let uu____4880
                                                                    =
                                                                    let uu____4881
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4881
                                                                     in
                                                                    ((fun
                                                                    uu____4886
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____4880)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4872
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____4871,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____4907
                                                                    =
                                                                    let uu____4919
                                                                    =
                                                                    let uu____4929
                                                                    =
                                                                    let uu____4930
                                                                    =
                                                                    let uu____4938
                                                                    =
                                                                    let uu____4939
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4939
                                                                     in
                                                                    ((fun
                                                                    uu____4945
                                                                     ->
                                                                    (
                                                                    let uu____4947
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4947);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4938)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4930
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4929,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4919]
                                                                     in
                                                                    uu____4861
                                                                    ::
                                                                    uu____4907
                                                                     in
                                                                    uu____4803
                                                                    ::
                                                                    uu____4849
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4791
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4779
                                                                     in
                                                                    uu____4754
                                                                    ::
                                                                    uu____4767
                                                                     in
                                                                    uu____4729
                                                                    ::
                                                                    uu____4742
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4717
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4705
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4693
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4681
                                                                     in
                                                                    uu____4656
                                                                    ::
                                                                    uu____4669
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4644
                                                                     in
                                                                    uu____4619
                                                                    ::
                                                                    uu____4632
                                                                     in
                                                                    uu____4577
                                                                    ::
                                                                    uu____4607
                                                                     in
                                                                    uu____4552
                                                                    ::
                                                                    uu____4565
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4540
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4528
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4516
                                                                     in
                                                                    uu____4491
                                                                    ::
                                                                    uu____4504
                                                                     in
                                                                    uu____4466
                                                                    ::
                                                                    uu____4479
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4454
                                                                     in
                                                                    uu____4429
                                                                    ::
                                                                    uu____4442
                                                                     in
                                                                    uu____4404
                                                                    ::
                                                                    uu____4417
                                                                     in
                                                                    uu____4379
                                                                    ::
                                                                    uu____4392
                                                                     in
                                                                    uu____4354
                                                                    ::
                                                                    uu____4367
                                                                     in
                                                                    uu____4329
                                                                    ::
                                                                    uu____4342
                                                                     in
                                                                    uu____4304
                                                                    ::
                                                                    uu____4317
                                                                     in
                                                                    uu____4279
                                                                    ::
                                                                    uu____4292
                                                                     in
                                                                    uu____4254
                                                                    ::
                                                                    uu____4267
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____4242
                                                                     in
                                                                    uu____4217
                                                                    ::
                                                                    uu____4230
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4205
                                                                     in
                                                                    uu____4180
                                                                    ::
                                                                    uu____4193
                                                                     in
                                                                    uu____4155
                                                                    ::
                                                                    uu____4168
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4143
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4131
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4119
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4107
                                                                     in
                                                                    uu____4082
                                                                    ::
                                                                    uu____4095
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____4070
                                                                     in
                                                                    uu____4045
                                                                    ::
                                                                    uu____4058
                                                                     in
                                                                    uu____4020
                                                                    ::
                                                                    uu____4033
                                                                     in
                                                                    uu____3995
                                                                    ::
                                                                    uu____4008
                                                                     in
                                                                    uu____3970
                                                                    ::
                                                                    uu____3983
                                                                     in
                                                                    uu____3945
                                                                    ::
                                                                    uu____3958
                                                                     in
                                                                    uu____3920
                                                                    ::
                                                                    uu____3933
                                                                     in
                                                                    uu____3895
                                                                    ::
                                                                    uu____3908
                                                                     in
                                                                    uu____3870
                                                                    ::
                                                                    uu____3883
                                                                     in
                                                                    uu____3845
                                                                    ::
                                                                    uu____3858
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3833
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3821
                                                                     in
                                                                    uu____3796
                                                                    ::
                                                                    uu____3809
                                                                     in
                                                                    uu____3771
                                                                    ::
                                                                    uu____3784
                                                                     in
                                                                    uu____3746
                                                                    ::
                                                                    uu____3759
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3734
                                                                     in
                                                                    uu____3709
                                                                    ::
                                                                    uu____3722
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3697
                                                                     in
                                                                    uu____3672
                                                                    ::
                                                                    uu____3685
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3660
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3648
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3636
                                                                     in
                                                                    uu____3611
                                                                    ::
                                                                    uu____3624
                                                                     in
                                                                    uu____3586
                                                                    ::
                                                                    uu____3599
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3574
                                                                     in
                                                                  uu____3549
                                                                    ::
                                                                    uu____3562
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_ifuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                  ::
                                                                  uu____3537
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_fuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of recursive functions to try initially (default 2)")
                                                                :: uu____3525
                                                               in
                                                            uu____3500 ::
                                                              uu____3513
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "include",
                                                            (ReverseAccumulated
                                                               (PathStr
                                                                  "path")),
                                                            "A directory in which to search for files included on the command line")
                                                            :: uu____3488
                                                           in
                                                        uu____3463 ::
                                                          uu____3476
                                                         in
                                                      uu____3438 ::
                                                        uu____3451
                                                       in
                                                    uu____3413 :: uu____3426
                                                     in
                                                  (FStar_Getopt.noshort,
                                                    "hint_file",
                                                    (PathStr "path"),
                                                    "Read/write hints to <path> (instead of module-specific hints files)")
                                                    :: uu____3401
                                                   in
                                                uu____3376 :: uu____3389  in
                                              uu____3351 :: uu____3364  in
                                            (FStar_Getopt.noshort,
                                              "extract_namespace",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "namespace name")))),
                                              "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                              :: uu____3339
                                             in
                                          (FStar_Getopt.noshort,
                                            "extract_module",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr "module_name")))),
                                            "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                            :: uu____3327
                                           in
                                        (FStar_Getopt.noshort, "extract",
                                          (Accumulated
                                             (SimpleStr
                                                "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                          "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                          :: uu____3315
                                         in
                                      uu____3290 :: uu____3303  in
                                    uu____3265 :: uu____3278  in
                                  (FStar_Getopt.noshort, "dump_module",
                                    (Accumulated (SimpleStr "module_name")),
                                    "") :: uu____3253
                                   in
                                uu____3228 :: uu____3241  in
                              uu____3203 :: uu____3216  in
                            uu____3178 :: uu____3191  in
                          (FStar_Getopt.noshort, "dep",
                            (EnumStr ["make"; "graph"; "full"]),
                            "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                            :: uu____3166
                           in
                        (FStar_Getopt.noshort, "defensive",
                          (EnumStr ["no"; "warn"; "fail"]),
                          "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                          :: uu____3154
                         in
                      (FStar_Getopt.noshort, "debug_level",
                        (Accumulated
                           (OpenEnumStr
                              (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                        "Control the verbosity of debugging info") ::
                        uu____3142
                       in
                    (FStar_Getopt.noshort, "debug",
                      (Accumulated (SimpleStr "module_name")),
                      "Print lots of debugging information while checking module")
                      :: uu____3130
                     in
                  (FStar_Getopt.noshort, "codegen-lib",
                    (Accumulated (SimpleStr "namespace")),
                    "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                    :: uu____3118
                   in
                (FStar_Getopt.noshort, "codegen",
                  (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                  "Generate code for further compilation to executable code, or build a compiler plugin")
                  :: uu____3106
                 in
              uu____3081 :: uu____3094  in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____3069
             in
          uu____3044 :: uu____3057  in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____3032
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____3020
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___83_5910  ->
             match uu___83_5910 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____3008

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5933  ->
    let uu____5936 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5963  ->
         match uu____5963 with
         | (short,long,typ,doc) ->
             let uu____5979 =
               let uu____5991 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5991, doc)  in
             mk_spec uu____5979) uu____5936

let (settable : Prims.string -> Prims.bool) =
  fun uu___84_6001  ->
    match uu___84_6001 with
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
    | uu____6002 -> false
  
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
       (fun uu____6076  ->
          match uu____6076 with
          | (uu____6088,x,uu____6090,uu____6091) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____6153  ->
          match uu____6153 with
          | (uu____6165,x,uu____6167,uu____6168) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____6179  ->
    let uu____6180 = specs ()  in display_usage_aux uu____6180
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____6204 -> true
    | uu____6205 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____6212 -> uu____6212
  
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
        (fun uu___91_6229  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____6240 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____6240
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____6268  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____6273 =
             let uu____6276 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____6276 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____6273)
       in
    let uu____6325 =
      let uu____6328 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6328
       in
    (res, uu____6325)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6362  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6397 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6397 (fun x  -> ())  in
     (let uu____6403 =
        let uu____6408 =
          let uu____6409 = FStar_List.map mk_string old_verify_module  in
          List uu____6409  in
        ("verify_module", uu____6408)  in
      set_option' uu____6403);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6419 =
        let uu____6420 =
          let uu____6421 =
            let uu____6422 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6422  in
          (FStar_String.length f1) - uu____6421  in
        uu____6420 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6419  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6428 = get_lax ()  in
    if uu____6428
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6438 = module_name_of_file_name fn  in should_verify uu____6438
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6444 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6444
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6452 = should_verify m  in
    if uu____6452 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6460  ->
    let uu____6461 = get_no_default_includes ()  in
    if uu____6461
    then get_include ()
    else
      (let lib_paths =
         let uu____6468 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6468 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6477 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6477
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6491 =
         let uu____6494 = get_include ()  in
         FStar_List.append uu____6494 ["."]  in
       FStar_List.append lib_paths uu____6491)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____6507 = FStar_Util.smap_try_find file_map filename  in
    match uu____6507 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___93_6520  ->
               match () with
               | () ->
                   let uu____6523 = FStar_Util.is_path_absolute filename  in
                   if uu____6523
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____6530 =
                        let uu____6533 = include_path ()  in
                        FStar_List.rev uu____6533  in
                      FStar_Util.find_map uu____6530
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___92_6545 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____6556  ->
    let uu____6557 = get_prims ()  in
    match uu____6557 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6561 = find_file filename  in
        (match uu____6561 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6565 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6565)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6571  ->
    let uu____6572 = prims ()  in FStar_Util.basename uu____6572
  
let (pervasives : unit -> Prims.string) =
  fun uu____6577  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____6579 = find_file filename  in
    match uu____6579 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____6583 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6583
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6588  ->
    let uu____6589 = pervasives ()  in FStar_Util.basename uu____6589
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6594  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____6596 = find_file filename  in
    match uu____6596 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____6600 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6600
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____6606 = get_odir ()  in
    match uu____6606 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____6615 = get_cache_dir ()  in
    match uu____6615 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6619 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____6619
  
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
             let uu____6685 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____6685  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____6693 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6693 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6763 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6763 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6772  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6777  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6784  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6789  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____6794  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6800 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6806 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6812 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6818 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6825  ->
    let uu____6826 = get_codegen ()  in
    FStar_Util.map_opt uu____6826
      (fun uu___85_6830  ->
         match uu___85_6830 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6831 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6840  ->
    let uu____6841 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6841
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6858  -> let uu____6859 = get_debug ()  in uu____6859 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6869 = get_debug ()  in
    FStar_All.pipe_right uu____6869 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6886 = get_debug ()  in
       FStar_All.pipe_right uu____6886 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6895  -> let uu____6896 = get_defensive ()  in uu____6896 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6901  ->
    let uu____6902 = get_defensive ()  in uu____6902 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6909  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6914  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6919  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6924  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6930 = get_dump_module ()  in
    FStar_All.pipe_right uu____6930 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6939  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6944  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6950 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6950
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6980  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6985  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6990  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6997  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____7002  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____7007  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____7012  ->
    let uu____7013 = get_initial_fuel ()  in
    let uu____7014 = get_max_fuel ()  in Prims.min uu____7013 uu____7014
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____7019  ->
    let uu____7020 = get_initial_ifuel ()  in
    let uu____7021 = get_max_ifuel ()  in Prims.min uu____7020 uu____7021
  
let (interactive : unit -> Prims.bool) =
  fun uu____7026  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____7031  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____7038  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____7043  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____7048  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____7053  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____7058  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____7063  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____7068  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____7073  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____7078  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____7083  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____7088  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____7095 = get_no_extract ()  in
    FStar_All.pipe_right uu____7095
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____7106  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____7111  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____7116  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____7121  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7128  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____7133  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____7138  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____7143  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____7148  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____7153  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____7158  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____7163  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____7168  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____7173  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7180  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____7185  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____7190  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____7195  ->
    let uu____7196 = get_smtencoding_nl_arith_repr ()  in
    uu____7196 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____7201  ->
    let uu____7202 = get_smtencoding_nl_arith_repr ()  in
    uu____7202 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____7207  ->
    let uu____7208 = get_smtencoding_nl_arith_repr ()  in
    uu____7208 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____7213  ->
    let uu____7214 = get_smtencoding_l_arith_repr ()  in
    uu____7214 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____7219  ->
    let uu____7220 = get_smtencoding_l_arith_repr ()  in
    uu____7220 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____7225  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____7230  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____7235  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____7240  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____7245  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____7250  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____7255  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____7260  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____7265  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____7270  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____7275  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____7280  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7287  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____7292  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____7305  ->
    let uu____7306 = get_using_facts_from ()  in
    match uu____7306 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7344  ->
    let uu____7345 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____7345
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7352  ->
    let uu____7353 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____7353 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7356 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7363  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____7368  ->
    let uu____7369 = get_smt ()  in
    match uu____7369 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7379  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____7384  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____7389  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7394  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____7399  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7404  ->
    (get_use_two_phase_tc ()) &&
      (let uu____7406 = lax ()  in Prims.op_Negation uu____7406)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7411  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7416  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7421  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7426  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7433 = get_extract ()  in
    match uu____7433 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7444 =
            let uu____7457 = get_no_extract ()  in
            let uu____7460 = get_extract_namespace ()  in
            let uu____7463 = get_extract_module ()  in
            (uu____7457, uu____7460, uu____7463)  in
          match uu____7444 with
          | ([],[],[]) -> ()
          | uu____7478 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7526,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7545 -> false  in
          let uu____7554 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7588  ->
                    match uu____7588 with
                    | (path,uu____7596) -> matches_path m_components path))
             in
          match uu____7554 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____7607,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____7627 = get_extract_namespace ()  in
          match uu____7627 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____7643 = get_extract_module ()  in
          match uu____7643 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____7655 = no_extract m1  in Prims.op_Negation uu____7655) &&
          (let uu____7657 =
             let uu____7666 = get_extract_namespace ()  in
             let uu____7669 = get_extract_module ()  in
             (uu____7666, uu____7669)  in
           (match uu____7657 with
            | ([],[]) -> true
            | uu____7680 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  