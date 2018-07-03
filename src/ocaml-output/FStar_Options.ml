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
  fun uu___75_332  ->
    match uu___75_332 with
    | Bool b -> b
    | uu____334 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___76_339  ->
    match uu___76_339 with
    | Int b -> b
    | uu____341 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___77_346  ->
    match uu___77_346 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____349 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___78_356  ->
    match uu___78_356 with
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
    fun uu___79_417  ->
      match uu___79_417 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____421 = as_t v1  in FStar_Pervasives_Native.Some uu____421
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___80_428  ->
    match uu___80_428 with
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
  fun f  -> push (); (let retv = f ()  in pop (); retv) 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____768 =
      let uu____771 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____771
       in
    FStar_ST.op_Colon_Equals light_off_files uu____768
  
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
  fun uu____1226  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1243  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1300 =
      let uu____1303 = peek ()  in FStar_Util.smap_try_find uu____1303 s  in
    match uu____1300 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1313 . Prims.string -> (option_val -> 'Auu____1313) -> 'Auu____1313
  = fun s  -> fun c  -> let uu____1329 = get_option s  in c uu____1329 
let (get_abort_on : unit -> Prims.int) =
  fun uu____1334  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1339  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1346  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1353  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1360  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1367  -> lookup_opt "cache_off" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1374  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1383  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1392  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1401  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____1408  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1415  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1422  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1427  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1432  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1439  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1446  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1451  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1460  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1473  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1482  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1489  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1494  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1499  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1506  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1513  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1518  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1525  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1532  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1537  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1542  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1547  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1554  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1561  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1566  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1571  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1576  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1581  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1586  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1591  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1596  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1603  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1610  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1615  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1620  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1627  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1634  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1641  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1648  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1653  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1658  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1663  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1668  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1673  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1678  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1683  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1688  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1695  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1702  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1709  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1716  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1721  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1726  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1731  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1736  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1741  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____1746  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____1751  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____1756  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1761  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1766  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1771  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1776  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1781  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1786  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1793  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1800  ->
    let uu____1801 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1801
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1810  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1823  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1832  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1841  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1848  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1853  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1860  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1867  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1872  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1877  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1882  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1887  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1892  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1897  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1902  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1907  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___81_1912  ->
    match uu___81_1912 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1924 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1930 = get_debug_level ()  in
    FStar_All.pipe_right uu____1930
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2063  ->
    let uu____2064 =
      let uu____2065 = FStar_ST.op_Bang _version  in
      let uu____2085 = FStar_ST.op_Bang _platform  in
      let uu____2105 = FStar_ST.op_Bang _compiler  in
      let uu____2125 = FStar_ST.op_Bang _date  in
      let uu____2145 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2065
        uu____2085 uu____2105 uu____2125 uu____2145
       in
    FStar_Util.print_string uu____2064
  
let display_usage_aux :
  'Auu____2171 'Auu____2172 .
    ('Auu____2171,Prims.string,'Auu____2172 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2220  ->
         match uu____2220 with
         | (uu____2231,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2243 =
                      let uu____2244 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2244  in
                    FStar_Util.print_string uu____2243
                  else
                    (let uu____2246 =
                       let uu____2247 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2247 doc  in
                     FStar_Util.print_string uu____2246)
              | FStar_Getopt.OneArg (uu____2248,argname) ->
                  if doc = ""
                  then
                    let uu____2256 =
                      let uu____2257 = FStar_Util.colorize_bold flag  in
                      let uu____2258 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2257 uu____2258
                       in
                    FStar_Util.print_string uu____2256
                  else
                    (let uu____2260 =
                       let uu____2261 = FStar_Util.colorize_bold flag  in
                       let uu____2262 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2261
                         uu____2262 doc
                        in
                     FStar_Util.print_string uu____2260))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2290 = o  in
    match uu____2290 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2326 =
                let uu____2327 = f ()  in set_option name uu____2327  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2342 = f x  in set_option name uu____2342
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2362 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2362  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2385 =
        let uu____2388 = lookup_opt name as_list'  in
        FStar_List.append uu____2388 [value]  in
      mk_list uu____2385
  
let accumulate_string :
  'Auu____2401 .
    Prims.string -> ('Auu____2401 -> Prims.string) -> 'Auu____2401 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2422 =
          let uu____2423 =
            let uu____2424 = post_processor value  in mk_string uu____2424
             in
          accumulated_option name uu____2423  in
        set_option name uu____2422
  
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
    match projectee with | Const _0 -> true | uu____2520 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2534 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2547 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2554 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2568 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2584 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2610 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2649 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2684 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2698 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2719 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2757 -> true
    | uu____2758 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2765 -> uu____2765
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___86_2783  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____2785 ->
                      let uu____2786 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____2786 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____2790 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____2790
                  | PathStr uu____2793 -> mk_path str_val
                  | SimpleStr uu____2794 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____2799 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____2814 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____2814
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
            let uu____2833 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2833
  
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
    | PostProcessed (uu____2870,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2880,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2907 = desc_of_opt_type typ  in
      match uu____2907 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2913  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2930 =
      let uu____2931 = as_string s  in FStar_String.lowercase uu____2931  in
    mk_string uu____2930
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2979  ->
    let uu____2991 =
      let uu____3003 =
        let uu____3015 =
          let uu____3027 =
            let uu____3037 =
              let uu____3038 = mk_bool true  in Const uu____3038  in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____3037,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
             in
          let uu____3040 =
            let uu____3052 =
              let uu____3064 =
                let uu____3074 =
                  let uu____3075 = mk_bool true  in Const uu____3075  in
                (FStar_Getopt.noshort, "cache_off", uu____3074,
                  "Do not read or write any .checked files")
                 in
              let uu____3077 =
                let uu____3089 =
                  let uu____3101 =
                    let uu____3113 =
                      let uu____3125 =
                        let uu____3137 =
                          let uu____3149 =
                            let uu____3161 =
                              let uu____3171 =
                                let uu____3172 = mk_bool true  in
                                Const uu____3172  in
                              (FStar_Getopt.noshort, "detail_errors",
                                uu____3171,
                                "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                               in
                            let uu____3174 =
                              let uu____3186 =
                                let uu____3196 =
                                  let uu____3197 = mk_bool true  in
                                  Const uu____3197  in
                                (FStar_Getopt.noshort, "detail_hint_replay",
                                  uu____3196,
                                  "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                 in
                              let uu____3199 =
                                let uu____3211 =
                                  let uu____3221 =
                                    let uu____3222 = mk_bool true  in
                                    Const uu____3222  in
                                  (FStar_Getopt.noshort, "doc", uu____3221,
                                    "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                   in
                                let uu____3224 =
                                  let uu____3236 =
                                    let uu____3248 =
                                      let uu____3258 =
                                        let uu____3259 = mk_bool true  in
                                        Const uu____3259  in
                                      (FStar_Getopt.noshort,
                                        "eager_inference", uu____3258,
                                        "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                       in
                                    let uu____3261 =
                                      let uu____3273 =
                                        let uu____3283 =
                                          let uu____3284 = mk_bool true  in
                                          Const uu____3284  in
                                        (FStar_Getopt.noshort,
                                          "eager_subtyping", uu____3283,
                                          "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                         in
                                      let uu____3286 =
                                        let uu____3298 =
                                          let uu____3310 =
                                            let uu____3322 =
                                              let uu____3334 =
                                                let uu____3344 =
                                                  let uu____3345 =
                                                    mk_bool true  in
                                                  Const uu____3345  in
                                                (FStar_Getopt.noshort,
                                                  "expose_interfaces",
                                                  uu____3344,
                                                  "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                 in
                                              let uu____3347 =
                                                let uu____3359 =
                                                  let uu____3369 =
                                                    let uu____3370 =
                                                      mk_bool true  in
                                                    Const uu____3370  in
                                                  (FStar_Getopt.noshort,
                                                    "hide_uvar_nums",
                                                    uu____3369,
                                                    "Don't print unification variable numbers")
                                                   in
                                                let uu____3372 =
                                                  let uu____3384 =
                                                    let uu____3396 =
                                                      let uu____3406 =
                                                        let uu____3407 =
                                                          mk_bool true  in
                                                        Const uu____3407  in
                                                      (FStar_Getopt.noshort,
                                                        "hint_info",
                                                        uu____3406,
                                                        "Print information regarding hints (deprecated; use --query_stats instead)")
                                                       in
                                                    let uu____3409 =
                                                      let uu____3421 =
                                                        let uu____3431 =
                                                          let uu____3432 =
                                                            mk_bool true  in
                                                          Const uu____3432
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "in", uu____3431,
                                                          "Legacy interactive mode; reads input from stdin")
                                                         in
                                                      let uu____3434 =
                                                        let uu____3446 =
                                                          let uu____3456 =
                                                            let uu____3457 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3457
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "ide",
                                                            uu____3456,
                                                            "JSON-based interactive mode for IDEs")
                                                           in
                                                        let uu____3459 =
                                                          let uu____3471 =
                                                            let uu____3483 =
                                                              let uu____3493
                                                                =
                                                                let uu____3494
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____3494
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "indent",
                                                                uu____3493,
                                                                "Parses and outputs the files on the command line")
                                                               in
                                                            let uu____3496 =
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
                                                                    "lax",
                                                                    uu____3542,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                  let uu____3545
                                                                    =
                                                                    let uu____3557
                                                                    =
                                                                    let uu____3569
                                                                    =
                                                                    let uu____3579
                                                                    =
                                                                    let uu____3580
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3580
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3579,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3582
                                                                    =
                                                                    let uu____3594
                                                                    =
                                                                    let uu____3604
                                                                    =
                                                                    let uu____3605
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3605
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3604,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3607
                                                                    =
                                                                    let uu____3619
                                                                    =
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
                                                                    "MLish",
                                                                    uu____3665,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
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
                                                                    "no_default_includes",
                                                                    uu____3702,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3705
                                                                    =
                                                                    let uu____3717
                                                                    =
                                                                    let uu____3729
                                                                    =
                                                                    let uu____3739
                                                                    =
                                                                    let uu____3740
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3740
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3739,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3742
                                                                    =
                                                                    let uu____3754
                                                                    =
                                                                    let uu____3764
                                                                    =
                                                                    let uu____3765
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3765
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3764,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3767
                                                                    =
                                                                    let uu____3779
                                                                    =
                                                                    let uu____3789
                                                                    =
                                                                    let uu____3790
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3790
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3789,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3792
                                                                    =
                                                                    let uu____3804
                                                                    =
                                                                    let uu____3816
                                                                    =
                                                                    let uu____3828
                                                                    =
                                                                    let uu____3838
                                                                    =
                                                                    let uu____3839
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3839
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3838,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3841
                                                                    =
                                                                    let uu____3853
                                                                    =
                                                                    let uu____3863
                                                                    =
                                                                    let uu____3864
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3864
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3863,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3866
                                                                    =
                                                                    let uu____3878
                                                                    =
                                                                    let uu____3888
                                                                    =
                                                                    let uu____3889
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3889
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3888,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3891
                                                                    =
                                                                    let uu____3903
                                                                    =
                                                                    let uu____3913
                                                                    =
                                                                    let uu____3914
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3914
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3913,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3916
                                                                    =
                                                                    let uu____3928
                                                                    =
                                                                    let uu____3938
                                                                    =
                                                                    let uu____3939
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3939
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3938,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3941
                                                                    =
                                                                    let uu____3953
                                                                    =
                                                                    let uu____3963
                                                                    =
                                                                    let uu____3964
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3964
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3963,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3966
                                                                    =
                                                                    let uu____3978
                                                                    =
                                                                    let uu____3988
                                                                    =
                                                                    let uu____3989
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3989
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3988,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3991
                                                                    =
                                                                    let uu____4003
                                                                    =
                                                                    let uu____4013
                                                                    =
                                                                    let uu____4014
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4014
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____4013,
                                                                    "Print SMT query statistics")
                                                                     in
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
                                                                    "record_hints",
                                                                    uu____4038,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____4041
                                                                    =
                                                                    let uu____4053
                                                                    =
                                                                    let uu____4065
                                                                    =
                                                                    let uu____4075
                                                                    =
                                                                    let uu____4076
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4076
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4075,
                                                                    " ")  in
                                                                    let uu____4078
                                                                    =
                                                                    let uu____4090
                                                                    =
                                                                    let uu____4102
                                                                    =
                                                                    let uu____4114
                                                                    =
                                                                    let uu____4126
                                                                    =
                                                                    let uu____4138
                                                                    =
                                                                    let uu____4148
                                                                    =
                                                                    let uu____4149
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4149
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4148,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
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
                                                                    "tactic_trace",
                                                                    uu____4173,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4176
                                                                    =
                                                                    let uu____4188
                                                                    =
                                                                    let uu____4200
                                                                    =
                                                                    let uu____4210
                                                                    =
                                                                    let uu____4211
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4211
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____4210,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____4213
                                                                    =
                                                                    let uu____4225
                                                                    =
                                                                    let uu____4237
                                                                    =
                                                                    let uu____4247
                                                                    =
                                                                    let uu____4248
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4248
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4247,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4250
                                                                    =
                                                                    let uu____4262
                                                                    =
                                                                    let uu____4272
                                                                    =
                                                                    let uu____4273
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4273
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4272,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4275
                                                                    =
                                                                    let uu____4287
                                                                    =
                                                                    let uu____4297
                                                                    =
                                                                    let uu____4298
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4298
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4297,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4300
                                                                    =
                                                                    let uu____4312
                                                                    =
                                                                    let uu____4322
                                                                    =
                                                                    let uu____4323
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4323
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4322,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4325
                                                                    =
                                                                    let uu____4337
                                                                    =
                                                                    let uu____4347
                                                                    =
                                                                    let uu____4348
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4348
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4347,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4350
                                                                    =
                                                                    let uu____4362
                                                                    =
                                                                    let uu____4372
                                                                    =
                                                                    let uu____4373
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4373
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4372,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4375
                                                                    =
                                                                    let uu____4387
                                                                    =
                                                                    let uu____4397
                                                                    =
                                                                    let uu____4398
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4398
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4397,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4400
                                                                    =
                                                                    let uu____4412
                                                                    =
                                                                    let uu____4422
                                                                    =
                                                                    let uu____4423
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4423
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4422,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4425
                                                                    =
                                                                    let uu____4437
                                                                    =
                                                                    let uu____4449
                                                                    =
                                                                    let uu____4459
                                                                    =
                                                                    let uu____4460
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4460
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4459,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4462
                                                                    =
                                                                    let uu____4474
                                                                    =
                                                                    let uu____4486
                                                                    =
                                                                    let uu____4498
                                                                    =
                                                                    let uu____4510
                                                                    =
                                                                    let uu____4520
                                                                    =
                                                                    let uu____4521
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4521
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4520,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4523
                                                                    =
                                                                    let uu____4535
                                                                    =
                                                                    let uu____4545
                                                                    =
                                                                    let uu____4546
                                                                    =
                                                                    let uu____4554
                                                                    =
                                                                    let uu____4555
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4555
                                                                     in
                                                                    ((fun
                                                                    uu____4561
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4554)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4546
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4545,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4565
                                                                    =
                                                                    let uu____4577
                                                                    =
                                                                    let uu____4587
                                                                    =
                                                                    let uu____4588
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4588
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4587,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4590
                                                                    =
                                                                    let uu____4602
                                                                    =
                                                                    let uu____4614
                                                                    =
                                                                    let uu____4624
                                                                    =
                                                                    let uu____4625
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4625
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4624,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4627
                                                                    =
                                                                    let uu____4639
                                                                    =
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
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4698
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4697,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4700
                                                                    =
                                                                    let uu____4712
                                                                    =
                                                                    let uu____4722
                                                                    =
                                                                    let uu____4723
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4723
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4722,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4725
                                                                    =
                                                                    let uu____4737
                                                                    =
                                                                    let uu____4749
                                                                    =
                                                                    let uu____4761
                                                                    =
                                                                    let uu____4771
                                                                    =
                                                                    let uu____4772
                                                                    =
                                                                    let uu____4780
                                                                    =
                                                                    let uu____4781
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4781
                                                                     in
                                                                    ((fun
                                                                    uu____4786
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____4780)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4772
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____4771,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____4807
                                                                    =
                                                                    let uu____4819
                                                                    =
                                                                    let uu____4829
                                                                    =
                                                                    let uu____4830
                                                                    =
                                                                    let uu____4838
                                                                    =
                                                                    let uu____4839
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4839
                                                                     in
                                                                    ((fun
                                                                    uu____4844
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____4838)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4830
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____4829,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____4865
                                                                    =
                                                                    let uu____4877
                                                                    =
                                                                    let uu____4887
                                                                    =
                                                                    let uu____4888
                                                                    =
                                                                    let uu____4896
                                                                    =
                                                                    let uu____4897
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4897
                                                                     in
                                                                    ((fun
                                                                    uu____4903
                                                                     ->
                                                                    (
                                                                    let uu____4905
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4905);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4896)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4888
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4887,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4877]
                                                                     in
                                                                    uu____4819
                                                                    ::
                                                                    uu____4865
                                                                     in
                                                                    uu____4761
                                                                    ::
                                                                    uu____4807
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4749
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4737
                                                                     in
                                                                    uu____4712
                                                                    ::
                                                                    uu____4725
                                                                     in
                                                                    uu____4687
                                                                    ::
                                                                    uu____4700
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4675
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4663
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4651
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4639
                                                                     in
                                                                    uu____4614
                                                                    ::
                                                                    uu____4627
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4602
                                                                     in
                                                                    uu____4577
                                                                    ::
                                                                    uu____4590
                                                                     in
                                                                    uu____4535
                                                                    ::
                                                                    uu____4565
                                                                     in
                                                                    uu____4510
                                                                    ::
                                                                    uu____4523
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4498
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4486
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4474
                                                                     in
                                                                    uu____4449
                                                                    ::
                                                                    uu____4462
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4437
                                                                     in
                                                                    uu____4412
                                                                    ::
                                                                    uu____4425
                                                                     in
                                                                    uu____4387
                                                                    ::
                                                                    uu____4400
                                                                     in
                                                                    uu____4362
                                                                    ::
                                                                    uu____4375
                                                                     in
                                                                    uu____4337
                                                                    ::
                                                                    uu____4350
                                                                     in
                                                                    uu____4312
                                                                    ::
                                                                    uu____4325
                                                                     in
                                                                    uu____4287
                                                                    ::
                                                                    uu____4300
                                                                     in
                                                                    uu____4262
                                                                    ::
                                                                    uu____4275
                                                                     in
                                                                    uu____4237
                                                                    ::
                                                                    uu____4250
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____4225
                                                                     in
                                                                    uu____4200
                                                                    ::
                                                                    uu____4213
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4188
                                                                     in
                                                                    uu____4163
                                                                    ::
                                                                    uu____4176
                                                                     in
                                                                    uu____4138
                                                                    ::
                                                                    uu____4151
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4126
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4114
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4102
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4090
                                                                     in
                                                                    uu____4065
                                                                    ::
                                                                    uu____4078
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____4053
                                                                     in
                                                                    uu____4028
                                                                    ::
                                                                    uu____4041
                                                                     in
                                                                    uu____4003
                                                                    ::
                                                                    uu____4016
                                                                     in
                                                                    uu____3978
                                                                    ::
                                                                    uu____3991
                                                                     in
                                                                    uu____3953
                                                                    ::
                                                                    uu____3966
                                                                     in
                                                                    uu____3928
                                                                    ::
                                                                    uu____3941
                                                                     in
                                                                    uu____3903
                                                                    ::
                                                                    uu____3916
                                                                     in
                                                                    uu____3878
                                                                    ::
                                                                    uu____3891
                                                                     in
                                                                    uu____3853
                                                                    ::
                                                                    uu____3866
                                                                     in
                                                                    uu____3828
                                                                    ::
                                                                    uu____3841
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3816
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3804
                                                                     in
                                                                    uu____3779
                                                                    ::
                                                                    uu____3792
                                                                     in
                                                                    uu____3754
                                                                    ::
                                                                    uu____3767
                                                                     in
                                                                    uu____3729
                                                                    ::
                                                                    uu____3742
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3717
                                                                     in
                                                                    uu____3692
                                                                    ::
                                                                    uu____3705
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3680
                                                                     in
                                                                    uu____3655
                                                                    ::
                                                                    uu____3668
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3643
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3631
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3619
                                                                     in
                                                                    uu____3594
                                                                    ::
                                                                    uu____3607
                                                                     in
                                                                    uu____3569
                                                                    ::
                                                                    uu____3582
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3557
                                                                     in
                                                                  uu____3532
                                                                    ::
                                                                    uu____3545
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_ifuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                  ::
                                                                  uu____3520
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_fuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of recursive functions to try initially (default 2)")
                                                                :: uu____3508
                                                               in
                                                            uu____3483 ::
                                                              uu____3496
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "include",
                                                            (ReverseAccumulated
                                                               (PathStr
                                                                  "path")),
                                                            "A directory in which to search for files included on the command line")
                                                            :: uu____3471
                                                           in
                                                        uu____3446 ::
                                                          uu____3459
                                                         in
                                                      uu____3421 ::
                                                        uu____3434
                                                       in
                                                    uu____3396 :: uu____3409
                                                     in
                                                  (FStar_Getopt.noshort,
                                                    "hint_file",
                                                    (PathStr "path"),
                                                    "Read/write hints to <path> (instead of module-specific hints files)")
                                                    :: uu____3384
                                                   in
                                                uu____3359 :: uu____3372  in
                                              uu____3334 :: uu____3347  in
                                            (FStar_Getopt.noshort,
                                              "extract_namespace",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "namespace name")))),
                                              "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                              :: uu____3322
                                             in
                                          (FStar_Getopt.noshort,
                                            "extract_module",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr "module_name")))),
                                            "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                            :: uu____3310
                                           in
                                        (FStar_Getopt.noshort, "extract",
                                          (Accumulated
                                             (SimpleStr
                                                "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                          "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                          :: uu____3298
                                         in
                                      uu____3273 :: uu____3286  in
                                    uu____3248 :: uu____3261  in
                                  (FStar_Getopt.noshort, "dump_module",
                                    (Accumulated (SimpleStr "module_name")),
                                    "") :: uu____3236
                                   in
                                uu____3211 :: uu____3224  in
                              uu____3186 :: uu____3199  in
                            uu____3161 :: uu____3174  in
                          (FStar_Getopt.noshort, "dep",
                            (EnumStr ["make"; "graph"; "full"]),
                            "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                            :: uu____3149
                           in
                        (FStar_Getopt.noshort, "defensive",
                          (EnumStr ["no"; "warn"; "fail"]),
                          "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                          :: uu____3137
                         in
                      (FStar_Getopt.noshort, "debug_level",
                        (Accumulated
                           (OpenEnumStr
                              (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                        "Control the verbosity of debugging info") ::
                        uu____3125
                       in
                    (FStar_Getopt.noshort, "debug",
                      (Accumulated (SimpleStr "module_name")),
                      "Print lots of debugging information while checking module")
                      :: uu____3113
                     in
                  (FStar_Getopt.noshort, "codegen-lib",
                    (Accumulated (SimpleStr "namespace")),
                    "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                    :: uu____3101
                   in
                (FStar_Getopt.noshort, "codegen",
                  (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                  "Generate code for further compilation to executable code, or build a compiler plugin")
                  :: uu____3089
                 in
              uu____3064 :: uu____3077  in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____3052
             in
          uu____3027 :: uu____3040  in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____3015
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____3003
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___82_5859  ->
             match uu___82_5859 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____2991

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5882  ->
    let uu____5885 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5912  ->
         match uu____5912 with
         | (short,long,typ,doc) ->
             let uu____5928 =
               let uu____5940 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5940, doc)  in
             mk_spec uu____5928) uu____5885

let (settable : Prims.string -> Prims.bool) =
  fun uu___83_5950  ->
    match uu___83_5950 with
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
    | uu____5951 -> false
  
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
       (fun uu____6025  ->
          match uu____6025 with
          | (uu____6037,x,uu____6039,uu____6040) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____6102  ->
          match uu____6102 with
          | (uu____6114,x,uu____6116,uu____6117) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____6128  ->
    let uu____6129 = specs ()  in display_usage_aux uu____6129
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____6153 -> true
    | uu____6154 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____6161 -> uu____6161
  
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
        (fun uu___88_6178  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____6189 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____6189
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____6217  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____6222 =
             let uu____6225 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____6225 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____6222)
       in
    let uu____6274 =
      let uu____6277 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6277
       in
    (res, uu____6274)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6311  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6346 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6346 (fun x  -> ())  in
     (let uu____6352 =
        let uu____6357 =
          let uu____6358 = FStar_List.map mk_string old_verify_module  in
          List uu____6358  in
        ("verify_module", uu____6357)  in
      set_option' uu____6352);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6368 =
        let uu____6369 =
          let uu____6370 =
            let uu____6371 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6371  in
          (FStar_String.length f1) - uu____6370  in
        uu____6369 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6368  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6377 = get_lax ()  in
    if uu____6377
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6387 = module_name_of_file_name fn  in should_verify uu____6387
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6393 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6393
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6401 = should_verify m  in
    if uu____6401 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6409  ->
    let uu____6410 = get_no_default_includes ()  in
    if uu____6410
    then get_include ()
    else
      (let lib_paths =
         let uu____6417 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6417 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6426 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6426
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6440 =
         let uu____6443 = get_include ()  in
         FStar_List.append uu____6443 ["."]  in
       FStar_List.append lib_paths uu____6440)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____6456 = FStar_Util.smap_try_find file_map filename  in
    match uu____6456 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___90_6469  ->
               match () with
               | () ->
                   let uu____6472 = FStar_Util.is_path_absolute filename  in
                   if uu____6472
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____6479 =
                        let uu____6482 = include_path ()  in
                        FStar_List.rev uu____6482  in
                      FStar_Util.find_map uu____6479
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu____6498 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____6507  ->
    let uu____6508 = get_prims ()  in
    match uu____6508 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6512 = find_file filename  in
        (match uu____6512 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6516 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6516)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6522  ->
    let uu____6523 = prims ()  in FStar_Util.basename uu____6523
  
let (pervasives : unit -> Prims.string) =
  fun uu____6528  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____6530 = find_file filename  in
    match uu____6530 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____6534 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6534
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6539  ->
    let uu____6540 = pervasives ()  in FStar_Util.basename uu____6540
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6545  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____6547 = find_file filename  in
    match uu____6547 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____6551 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6551
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____6557 = get_odir ()  in
    match uu____6557 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____6566 = get_cache_dir ()  in
    match uu____6566 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6570 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____6570
  
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
             let uu____6636 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____6636  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____6644 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6644 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6714 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6714 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6723  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6728  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6735  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6740  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____6745  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6751 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6757 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6763 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6769 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6776  ->
    let uu____6777 = get_codegen ()  in
    FStar_Util.map_opt uu____6777
      (fun uu___84_6781  ->
         match uu___84_6781 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6782 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6791  ->
    let uu____6792 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6792
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6809  -> let uu____6810 = get_debug ()  in uu____6810 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6820 = get_debug ()  in
    FStar_All.pipe_right uu____6820 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6837 = get_debug ()  in
       FStar_All.pipe_right uu____6837 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6846  -> let uu____6847 = get_defensive ()  in uu____6847 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6852  ->
    let uu____6853 = get_defensive ()  in uu____6853 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6860  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6865  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6870  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6875  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6881 = get_dump_module ()  in
    FStar_All.pipe_right uu____6881 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6890  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6895  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6901 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6901
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6931  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6936  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6941  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6948  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6953  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6958  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6963  ->
    let uu____6964 = get_initial_fuel ()  in
    let uu____6965 = get_max_fuel ()  in Prims.min uu____6964 uu____6965
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6970  ->
    let uu____6971 = get_initial_ifuel ()  in
    let uu____6972 = get_max_ifuel ()  in Prims.min uu____6971 uu____6972
  
let (interactive : unit -> Prims.bool) =
  fun uu____6977  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6982  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6989  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6994  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6999  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____7004  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____7009  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____7014  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____7019  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____7024  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____7029  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____7034  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____7039  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____7046 = get_no_extract ()  in
    FStar_All.pipe_right uu____7046
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____7057  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____7062  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____7067  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7074  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____7079  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____7084  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____7089  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____7094  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____7099  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____7104  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____7109  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____7114  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____7119  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7126  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____7131  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____7136  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____7141  ->
    let uu____7142 = get_smtencoding_nl_arith_repr ()  in
    uu____7142 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____7147  ->
    let uu____7148 = get_smtencoding_nl_arith_repr ()  in
    uu____7148 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____7153  ->
    let uu____7154 = get_smtencoding_nl_arith_repr ()  in
    uu____7154 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____7159  ->
    let uu____7160 = get_smtencoding_l_arith_repr ()  in
    uu____7160 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____7165  ->
    let uu____7166 = get_smtencoding_l_arith_repr ()  in
    uu____7166 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____7171  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____7176  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____7181  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____7186  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____7191  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____7196  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____7201  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____7206  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____7211  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____7216  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____7221  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____7226  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7233  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____7238  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____7251  ->
    let uu____7252 = get_using_facts_from ()  in
    match uu____7252 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7290  ->
    let uu____7291 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____7291
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7298  ->
    let uu____7299 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____7299 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7302 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7309  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____7314  ->
    let uu____7315 = get_smt ()  in
    match uu____7315 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7325  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____7330  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____7335  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7340  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____7345  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7350  ->
    (get_use_two_phase_tc ()) &&
      (let uu____7352 = lax ()  in Prims.op_Negation uu____7352)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7357  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7362  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7367  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7372  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7379 = get_extract ()  in
    match uu____7379 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7390 =
            let uu____7403 = get_no_extract ()  in
            let uu____7406 = get_extract_namespace ()  in
            let uu____7409 = get_extract_module ()  in
            (uu____7403, uu____7406, uu____7409)  in
          match uu____7390 with
          | ([],[],[]) -> ()
          | uu____7424 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7472,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7491 -> false  in
          let uu____7500 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7534  ->
                    match uu____7534 with
                    | (path,uu____7542) -> matches_path m_components path))
             in
          match uu____7500 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____7553,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____7573 = get_extract_namespace ()  in
          match uu____7573 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____7589 = get_extract_module ()  in
          match uu____7589 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____7601 = no_extract m1  in Prims.op_Negation uu____7601) &&
          (let uu____7603 =
             let uu____7612 = get_extract_namespace ()  in
             let uu____7615 = get_extract_module ()  in
             (uu____7612, uu____7615)  in
           (match uu____7603 with
            | ([],[]) -> true
            | uu____7626 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  