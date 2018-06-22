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
  fun uu___75_296  ->
    match uu___75_296 with
    | Bool b -> b
    | uu____298 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___76_303  ->
    match uu___76_303 with
    | Int b -> b
    | uu____305 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___77_310  ->
    match uu___77_310 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____313 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___78_320  ->
    match uu___78_320 with
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
    fun uu___79_381  ->
      match uu___79_381 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____385 = as_t v1  in FStar_Pervasives_Native.Some uu____385
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___80_392  ->
    match uu___80_392 with
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
  ("warn_error", (String ""));
  ("use_extracted_interfaces", (Bool false))] 
let (init : unit -> unit) =
  fun uu____1218  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1235  ->
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
let (get_timing : unit -> Prims.bool) =
  fun uu____1746  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1751  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1756  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1761  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1766  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1771  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1776  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1783  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1790  ->
    let uu____1791 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1791
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1800  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1813  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1822  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1831  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1838  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1843  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1850  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1857  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1862  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1867  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1872  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1877  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1882  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1887  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1892  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1897  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___81_1902  ->
    match uu___81_1902 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1914 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1920 = get_debug_level ()  in
    FStar_All.pipe_right uu____1920
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2053  ->
    let uu____2054 =
      let uu____2055 = FStar_ST.op_Bang _version  in
      let uu____2079 = FStar_ST.op_Bang _platform  in
      let uu____2103 = FStar_ST.op_Bang _compiler  in
      let uu____2127 = FStar_ST.op_Bang _date  in
      let uu____2151 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2055
        uu____2079 uu____2103 uu____2127 uu____2151
       in
    FStar_Util.print_string uu____2054
  
let display_usage_aux :
  'Auu____2181 'Auu____2182 .
    ('Auu____2181,Prims.string,'Auu____2182 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2230  ->
         match uu____2230 with
         | (uu____2241,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2253 =
                      let uu____2254 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2254  in
                    FStar_Util.print_string uu____2253
                  else
                    (let uu____2256 =
                       let uu____2257 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2257 doc  in
                     FStar_Util.print_string uu____2256)
              | FStar_Getopt.OneArg (uu____2258,argname) ->
                  if doc = ""
                  then
                    let uu____2266 =
                      let uu____2267 = FStar_Util.colorize_bold flag  in
                      let uu____2268 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2267 uu____2268
                       in
                    FStar_Util.print_string uu____2266
                  else
                    (let uu____2270 =
                       let uu____2271 = FStar_Util.colorize_bold flag  in
                       let uu____2272 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2271
                         uu____2272 doc
                        in
                     FStar_Util.print_string uu____2270))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2300 = o  in
    match uu____2300 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2336 =
                let uu____2337 = f ()  in set_option name uu____2337  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2352 = f x  in set_option name uu____2352
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2372 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2372  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2395 =
        let uu____2398 = lookup_opt name as_list'  in
        FStar_List.append uu____2398 [value]  in
      mk_list uu____2395
  
let accumulate_string :
  'Auu____2411 .
    Prims.string -> ('Auu____2411 -> Prims.string) -> 'Auu____2411 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2432 =
          let uu____2433 =
            let uu____2434 = post_processor value  in mk_string uu____2434
             in
          accumulated_option name uu____2433  in
        set_option name uu____2432
  
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
    match projectee with | Const _0 -> true | uu____2530 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2544 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2557 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2564 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2578 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2594 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2620 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2659 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2694 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2708 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2729 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2767 -> true
    | uu____2768 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2775 -> uu____2775
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2795 ->
              let uu____2796 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2796 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2800 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2800
          | PathStr uu____2803 -> mk_path str_val
          | SimpleStr uu____2804 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2809 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2824 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2824
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
            let uu____2843 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2843
  
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
    | PostProcessed (uu____2880,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2890,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2917 = desc_of_opt_type typ  in
      match uu____2917 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2923  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2940 =
      let uu____2941 = as_string s  in FStar_String.lowercase uu____2941  in
    mk_string uu____2940
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2989  ->
    let uu____3001 =
      let uu____3013 =
        let uu____3025 =
          let uu____3037 =
            let uu____3047 =
              let uu____3048 = mk_bool true  in Const uu____3048  in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____3047,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
             in
          let uu____3050 =
            let uu____3062 =
              let uu____3074 =
                let uu____3084 =
                  let uu____3085 = mk_bool true  in Const uu____3085  in
                (FStar_Getopt.noshort, "cache_off", uu____3084,
                  "Do not read or write any .checked files")
                 in
              let uu____3087 =
                let uu____3099 =
                  let uu____3111 =
                    let uu____3123 =
                      let uu____3135 =
                        let uu____3147 =
                          let uu____3159 =
                            let uu____3171 =
                              let uu____3181 =
                                let uu____3182 = mk_bool true  in
                                Const uu____3182  in
                              (FStar_Getopt.noshort, "detail_errors",
                                uu____3181,
                                "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                               in
                            let uu____3184 =
                              let uu____3196 =
                                let uu____3206 =
                                  let uu____3207 = mk_bool true  in
                                  Const uu____3207  in
                                (FStar_Getopt.noshort, "detail_hint_replay",
                                  uu____3206,
                                  "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                 in
                              let uu____3209 =
                                let uu____3221 =
                                  let uu____3231 =
                                    let uu____3232 = mk_bool true  in
                                    Const uu____3232  in
                                  (FStar_Getopt.noshort, "doc", uu____3231,
                                    "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                   in
                                let uu____3234 =
                                  let uu____3246 =
                                    let uu____3258 =
                                      let uu____3268 =
                                        let uu____3269 = mk_bool true  in
                                        Const uu____3269  in
                                      (FStar_Getopt.noshort,
                                        "eager_inference", uu____3268,
                                        "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                       in
                                    let uu____3271 =
                                      let uu____3283 =
                                        let uu____3293 =
                                          let uu____3294 = mk_bool true  in
                                          Const uu____3294  in
                                        (FStar_Getopt.noshort,
                                          "eager_subtyping", uu____3293,
                                          "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                         in
                                      let uu____3296 =
                                        let uu____3308 =
                                          let uu____3320 =
                                            let uu____3332 =
                                              let uu____3344 =
                                                let uu____3354 =
                                                  let uu____3355 =
                                                    mk_bool true  in
                                                  Const uu____3355  in
                                                (FStar_Getopt.noshort,
                                                  "expose_interfaces",
                                                  uu____3354,
                                                  "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                 in
                                              let uu____3357 =
                                                let uu____3369 =
                                                  let uu____3379 =
                                                    let uu____3380 =
                                                      mk_bool true  in
                                                    Const uu____3380  in
                                                  (FStar_Getopt.noshort,
                                                    "hide_uvar_nums",
                                                    uu____3379,
                                                    "Don't print unification variable numbers")
                                                   in
                                                let uu____3382 =
                                                  let uu____3394 =
                                                    let uu____3406 =
                                                      let uu____3416 =
                                                        let uu____3417 =
                                                          mk_bool true  in
                                                        Const uu____3417  in
                                                      (FStar_Getopt.noshort,
                                                        "hint_info",
                                                        uu____3416,
                                                        "Print information regarding hints (deprecated; use --query_stats instead)")
                                                       in
                                                    let uu____3419 =
                                                      let uu____3431 =
                                                        let uu____3441 =
                                                          let uu____3442 =
                                                            mk_bool true  in
                                                          Const uu____3442
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "in", uu____3441,
                                                          "Legacy interactive mode; reads input from stdin")
                                                         in
                                                      let uu____3444 =
                                                        let uu____3456 =
                                                          let uu____3466 =
                                                            let uu____3467 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3467
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "ide",
                                                            uu____3466,
                                                            "JSON-based interactive mode for IDEs")
                                                           in
                                                        let uu____3469 =
                                                          let uu____3481 =
                                                            let uu____3493 =
                                                              let uu____3503
                                                                =
                                                                let uu____3504
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____3504
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "indent",
                                                                uu____3503,
                                                                "Parses and outputs the files on the command line")
                                                               in
                                                            let uu____3506 =
                                                              let uu____3518
                                                                =
                                                                let uu____3530
                                                                  =
                                                                  let uu____3542
                                                                    =
                                                                    let uu____3552
                                                                    =
                                                                    let uu____3553
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3553
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3552,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                  let uu____3555
                                                                    =
                                                                    let uu____3567
                                                                    =
                                                                    let uu____3579
                                                                    =
                                                                    let uu____3589
                                                                    =
                                                                    let uu____3590
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3590
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3589,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3592
                                                                    =
                                                                    let uu____3604
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
                                                                    "log_queries",
                                                                    uu____3614,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3617
                                                                    =
                                                                    let uu____3629
                                                                    =
                                                                    let uu____3641
                                                                    =
                                                                    let uu____3653
                                                                    =
                                                                    let uu____3665
                                                                    =
                                                                    let uu____3675
                                                                    =
                                                                    let uu____3676
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3676
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3675,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3678
                                                                    =
                                                                    let uu____3690
                                                                    =
                                                                    let uu____3702
                                                                    =
                                                                    let uu____3712
                                                                    =
                                                                    let uu____3713
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3713
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3712,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3715
                                                                    =
                                                                    let uu____3727
                                                                    =
                                                                    let uu____3739
                                                                    =
                                                                    let uu____3749
                                                                    =
                                                                    let uu____3750
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3750
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3749,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3752
                                                                    =
                                                                    let uu____3764
                                                                    =
                                                                    let uu____3774
                                                                    =
                                                                    let uu____3775
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3775
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3774,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3777
                                                                    =
                                                                    let uu____3789
                                                                    =
                                                                    let uu____3799
                                                                    =
                                                                    let uu____3800
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3800
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3799,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3802
                                                                    =
                                                                    let uu____3814
                                                                    =
                                                                    let uu____3826
                                                                    =
                                                                    let uu____3838
                                                                    =
                                                                    let uu____3848
                                                                    =
                                                                    let uu____3849
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3849
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3848,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3851
                                                                    =
                                                                    let uu____3863
                                                                    =
                                                                    let uu____3873
                                                                    =
                                                                    let uu____3874
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3874
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3873,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3876
                                                                    =
                                                                    let uu____3888
                                                                    =
                                                                    let uu____3898
                                                                    =
                                                                    let uu____3899
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3899
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3898,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3901
                                                                    =
                                                                    let uu____3913
                                                                    =
                                                                    let uu____3923
                                                                    =
                                                                    let uu____3924
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3924
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3923,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3926
                                                                    =
                                                                    let uu____3938
                                                                    =
                                                                    let uu____3948
                                                                    =
                                                                    let uu____3949
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3949
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3948,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3951
                                                                    =
                                                                    let uu____3963
                                                                    =
                                                                    let uu____3973
                                                                    =
                                                                    let uu____3974
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3974
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3973,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3976
                                                                    =
                                                                    let uu____3988
                                                                    =
                                                                    let uu____3998
                                                                    =
                                                                    let uu____3999
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3999
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3998,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____4001
                                                                    =
                                                                    let uu____4013
                                                                    =
                                                                    let uu____4023
                                                                    =
                                                                    let uu____4024
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4024
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____4023,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____4026
                                                                    =
                                                                    let uu____4038
                                                                    =
                                                                    let uu____4048
                                                                    =
                                                                    let uu____4049
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4049
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____4048,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____4051
                                                                    =
                                                                    let uu____4063
                                                                    =
                                                                    let uu____4075
                                                                    =
                                                                    let uu____4085
                                                                    =
                                                                    let uu____4086
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4086
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4085,
                                                                    " ")  in
                                                                    let uu____4088
                                                                    =
                                                                    let uu____4100
                                                                    =
                                                                    let uu____4112
                                                                    =
                                                                    let uu____4124
                                                                    =
                                                                    let uu____4136
                                                                    =
                                                                    let uu____4148
                                                                    =
                                                                    let uu____4158
                                                                    =
                                                                    let uu____4159
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4159
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4158,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4161
                                                                    =
                                                                    let uu____4173
                                                                    =
                                                                    let uu____4183
                                                                    =
                                                                    let uu____4184
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4184
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4183,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4186
                                                                    =
                                                                    let uu____4198
                                                                    =
                                                                    let uu____4210
                                                                    =
                                                                    let uu____4220
                                                                    =
                                                                    let uu____4221
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4221
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4220,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4223
                                                                    =
                                                                    let uu____4235
                                                                    =
                                                                    let uu____4245
                                                                    =
                                                                    let uu____4246
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4246
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4245,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4248
                                                                    =
                                                                    let uu____4260
                                                                    =
                                                                    let uu____4270
                                                                    =
                                                                    let uu____4271
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4271
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4270,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4273
                                                                    =
                                                                    let uu____4285
                                                                    =
                                                                    let uu____4295
                                                                    =
                                                                    let uu____4296
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4296
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4295,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4298
                                                                    =
                                                                    let uu____4310
                                                                    =
                                                                    let uu____4320
                                                                    =
                                                                    let uu____4321
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4321
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4320,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4323
                                                                    =
                                                                    let uu____4335
                                                                    =
                                                                    let uu____4345
                                                                    =
                                                                    let uu____4346
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4346
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4345,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4348
                                                                    =
                                                                    let uu____4360
                                                                    =
                                                                    let uu____4370
                                                                    =
                                                                    let uu____4371
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4371
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4370,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4373
                                                                    =
                                                                    let uu____4385
                                                                    =
                                                                    let uu____4395
                                                                    =
                                                                    let uu____4396
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4396
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4395,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4398
                                                                    =
                                                                    let uu____4410
                                                                    =
                                                                    let uu____4422
                                                                    =
                                                                    let uu____4432
                                                                    =
                                                                    let uu____4433
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4433
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4432,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4435
                                                                    =
                                                                    let uu____4447
                                                                    =
                                                                    let uu____4459
                                                                    =
                                                                    let uu____4471
                                                                    =
                                                                    let uu____4483
                                                                    =
                                                                    let uu____4493
                                                                    =
                                                                    let uu____4494
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4494
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4493,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4496
                                                                    =
                                                                    let uu____4508
                                                                    =
                                                                    let uu____4518
                                                                    =
                                                                    let uu____4519
                                                                    =
                                                                    let uu____4527
                                                                    =
                                                                    let uu____4528
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4528
                                                                     in
                                                                    ((fun
                                                                    uu____4534
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4527)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4519
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4518,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4538
                                                                    =
                                                                    let uu____4550
                                                                    =
                                                                    let uu____4560
                                                                    =
                                                                    let uu____4561
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4561
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4560,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4563
                                                                    =
                                                                    let uu____4575
                                                                    =
                                                                    let uu____4587
                                                                    =
                                                                    let uu____4597
                                                                    =
                                                                    let uu____4598
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4598
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4597,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4600
                                                                    =
                                                                    let uu____4612
                                                                    =
                                                                    let uu____4624
                                                                    =
                                                                    let uu____4636
                                                                    =
                                                                    let uu____4648
                                                                    =
                                                                    let uu____4660
                                                                    =
                                                                    let uu____4670
                                                                    =
                                                                    let uu____4671
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4671
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4670,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4673
                                                                    =
                                                                    let uu____4685
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
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4695,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4698
                                                                    =
                                                                    let uu____4710
                                                                    =
                                                                    let uu____4722
                                                                    =
                                                                    let uu____4734
                                                                    =
                                                                    let uu____4744
                                                                    =
                                                                    let uu____4745
                                                                    =
                                                                    let uu____4753
                                                                    =
                                                                    let uu____4754
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4754
                                                                     in
                                                                    ((fun
                                                                    uu____4760
                                                                     ->
                                                                    (
                                                                    let uu____4762
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4762);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4753)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4745
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4744,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4734]
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4722
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4710
                                                                     in
                                                                    uu____4685
                                                                    ::
                                                                    uu____4698
                                                                     in
                                                                    uu____4660
                                                                    ::
                                                                    uu____4673
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4648
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4636
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4624
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4612
                                                                     in
                                                                    uu____4587
                                                                    ::
                                                                    uu____4600
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4575
                                                                     in
                                                                    uu____4550
                                                                    ::
                                                                    uu____4563
                                                                     in
                                                                    uu____4508
                                                                    ::
                                                                    uu____4538
                                                                     in
                                                                    uu____4483
                                                                    ::
                                                                    uu____4496
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4471
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4459
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4447
                                                                     in
                                                                    uu____4422
                                                                    ::
                                                                    uu____4435
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4410
                                                                     in
                                                                    uu____4385
                                                                    ::
                                                                    uu____4398
                                                                     in
                                                                    uu____4360
                                                                    ::
                                                                    uu____4373
                                                                     in
                                                                    uu____4335
                                                                    ::
                                                                    uu____4348
                                                                     in
                                                                    uu____4310
                                                                    ::
                                                                    uu____4323
                                                                     in
                                                                    uu____4285
                                                                    ::
                                                                    uu____4298
                                                                     in
                                                                    uu____4260
                                                                    ::
                                                                    uu____4273
                                                                     in
                                                                    uu____4235
                                                                    ::
                                                                    uu____4248
                                                                     in
                                                                    uu____4210
                                                                    ::
                                                                    uu____4223
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4198
                                                                     in
                                                                    uu____4173
                                                                    ::
                                                                    uu____4186
                                                                     in
                                                                    uu____4148
                                                                    ::
                                                                    uu____4161
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4136
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4124
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4112
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4100
                                                                     in
                                                                    uu____4075
                                                                    ::
                                                                    uu____4088
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____4063
                                                                     in
                                                                    uu____4038
                                                                    ::
                                                                    uu____4051
                                                                     in
                                                                    uu____4013
                                                                    ::
                                                                    uu____4026
                                                                     in
                                                                    uu____3988
                                                                    ::
                                                                    uu____4001
                                                                     in
                                                                    uu____3963
                                                                    ::
                                                                    uu____3976
                                                                     in
                                                                    uu____3938
                                                                    ::
                                                                    uu____3951
                                                                     in
                                                                    uu____3913
                                                                    ::
                                                                    uu____3926
                                                                     in
                                                                    uu____3888
                                                                    ::
                                                                    uu____3901
                                                                     in
                                                                    uu____3863
                                                                    ::
                                                                    uu____3876
                                                                     in
                                                                    uu____3838
                                                                    ::
                                                                    uu____3851
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3826
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3814
                                                                     in
                                                                    uu____3789
                                                                    ::
                                                                    uu____3802
                                                                     in
                                                                    uu____3764
                                                                    ::
                                                                    uu____3777
                                                                     in
                                                                    uu____3739
                                                                    ::
                                                                    uu____3752
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3727
                                                                     in
                                                                    uu____3702
                                                                    ::
                                                                    uu____3715
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3690
                                                                     in
                                                                    uu____3665
                                                                    ::
                                                                    uu____3678
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3653
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3641
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3629
                                                                     in
                                                                    uu____3604
                                                                    ::
                                                                    uu____3617
                                                                     in
                                                                    uu____3579
                                                                    ::
                                                                    uu____3592
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3567
                                                                     in
                                                                  uu____3542
                                                                    ::
                                                                    uu____3555
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_ifuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                  ::
                                                                  uu____3530
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_fuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of recursive functions to try initially (default 2)")
                                                                :: uu____3518
                                                               in
                                                            uu____3493 ::
                                                              uu____3506
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "include",
                                                            (ReverseAccumulated
                                                               (PathStr
                                                                  "path")),
                                                            "A directory in which to search for files included on the command line")
                                                            :: uu____3481
                                                           in
                                                        uu____3456 ::
                                                          uu____3469
                                                         in
                                                      uu____3431 ::
                                                        uu____3444
                                                       in
                                                    uu____3406 :: uu____3419
                                                     in
                                                  (FStar_Getopt.noshort,
                                                    "hint_file",
                                                    (PathStr "path"),
                                                    "Read/write hints to <path> (instead of module-specific hints files)")
                                                    :: uu____3394
                                                   in
                                                uu____3369 :: uu____3382  in
                                              uu____3344 :: uu____3357  in
                                            (FStar_Getopt.noshort,
                                              "extract_namespace",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "namespace name")))),
                                              "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                              :: uu____3332
                                             in
                                          (FStar_Getopt.noshort,
                                            "extract_module",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr "module_name")))),
                                            "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                            :: uu____3320
                                           in
                                        (FStar_Getopt.noshort, "extract",
                                          (Accumulated
                                             (SimpleStr
                                                "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                          "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                          :: uu____3308
                                         in
                                      uu____3283 :: uu____3296  in
                                    uu____3258 :: uu____3271  in
                                  (FStar_Getopt.noshort, "dump_module",
                                    (Accumulated (SimpleStr "module_name")),
                                    "") :: uu____3246
                                   in
                                uu____3221 :: uu____3234  in
                              uu____3196 :: uu____3209  in
                            uu____3171 :: uu____3184  in
                          (FStar_Getopt.noshort, "dep",
                            (EnumStr ["make"; "graph"; "full"]),
                            "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                            :: uu____3159
                           in
                        (FStar_Getopt.noshort, "defensive",
                          (EnumStr ["no"; "warn"; "fail"]),
                          "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                          :: uu____3147
                         in
                      (FStar_Getopt.noshort, "debug_level",
                        (Accumulated
                           (OpenEnumStr
                              (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                        "Control the verbosity of debugging info") ::
                        uu____3135
                       in
                    (FStar_Getopt.noshort, "debug",
                      (Accumulated (SimpleStr "module_name")),
                      "Print lots of debugging information while checking module")
                      :: uu____3123
                     in
                  (FStar_Getopt.noshort, "codegen-lib",
                    (Accumulated (SimpleStr "namespace")),
                    "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                    :: uu____3111
                   in
                (FStar_Getopt.noshort, "codegen",
                  (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                  "Generate code for further compilation to executable code, or build a compiler plugin")
                  :: uu____3099
                 in
              uu____3074 :: uu____3087  in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____3062
             in
          uu____3037 :: uu____3050  in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____3025
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____3013
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___82_5679  ->
             match uu___82_5679 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____3001

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5706  ->
    let uu____5709 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5736  ->
         match uu____5736 with
         | (short,long,typ,doc) ->
             let uu____5752 =
               let uu____5764 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5764, doc)  in
             mk_spec uu____5752) uu____5709

let (settable : Prims.string -> Prims.bool) =
  fun uu___83_5774  ->
    match uu___83_5774 with
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
    | "__temp_fast_implicits" -> true
    | "__temp_no_proj" -> true
    | "reuse_hint_for" -> true
    | "warn_error" -> true
    | "z3rlimit_factor" -> true
    | "z3rlimit" -> true
    | "z3refresh" -> true
    | "use_two_phase_tc" -> true
    | "vcgen.optimize_bind_as_seq" -> true
    | uu____5775 -> false
  
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
       (fun uu____5849  ->
          match uu____5849 with
          | (uu____5861,x,uu____5863,uu____5864) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5926  ->
          match uu____5926 with
          | (uu____5938,x,uu____5940,uu____5941) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5952  ->
    let uu____5953 = specs ()  in display_usage_aux uu____5953
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5977 -> true
    | uu____5978 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5985 -> uu____5985
  
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
          let uu____6013 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____6013
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____6041  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____6046 =
             let uu____6049 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____6049 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____6046)
       in
    let uu____6106 =
      let uu____6109 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6109
       in
    (res, uu____6106)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6147  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6186 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6186 (fun x  -> ())  in
     (let uu____6192 =
        let uu____6197 =
          let uu____6198 = FStar_List.map mk_string old_verify_module  in
          List uu____6198  in
        ("verify_module", uu____6197)  in
      set_option' uu____6192);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6208 =
        let uu____6209 =
          let uu____6210 =
            let uu____6211 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6211  in
          (FStar_String.length f1) - uu____6210  in
        uu____6209 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6208  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6217 = get_lax ()  in
    if uu____6217
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6227 = module_name_of_file_name fn  in should_verify uu____6227
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6233 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6233
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6241 = should_verify m  in
    if uu____6241 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6249  ->
    let uu____6250 = get_no_default_includes ()  in
    if uu____6250
    then get_include ()
    else
      (let lib_paths =
         let uu____6257 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6257 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6266 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6266
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6280 =
         let uu____6283 = get_include ()  in
         FStar_List.append uu____6283 ["."]  in
       FStar_List.append lib_paths uu____6280)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____6296 = FStar_Util.smap_try_find file_map filename  in
    match uu____6296 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            let uu____6312 = FStar_Util.is_path_absolute filename  in
            if uu____6312
            then
              (if FStar_Util.file_exists filename
               then FStar_Pervasives_Native.Some filename
               else FStar_Pervasives_Native.None)
            else
              (let uu____6319 =
                 let uu____6322 = include_path ()  in
                 FStar_List.rev uu____6322  in
               FStar_Util.find_map uu____6319
                 (fun p  ->
                    let path =
                      if p = "."
                      then filename
                      else FStar_Util.join_paths p filename  in
                    if FStar_Util.file_exists path
                    then FStar_Pervasives_Native.Some path
                    else FStar_Pervasives_Native.None))
          with | uu____6338 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____6347  ->
    let uu____6348 = get_prims ()  in
    match uu____6348 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6352 = find_file filename  in
        (match uu____6352 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6356 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6356)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6362  ->
    let uu____6363 = prims ()  in FStar_Util.basename uu____6363
  
let (pervasives : unit -> Prims.string) =
  fun uu____6368  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____6370 = find_file filename  in
    match uu____6370 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____6374 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6374
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6379  ->
    let uu____6380 = pervasives ()  in FStar_Util.basename uu____6380
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6385  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____6387 = find_file filename  in
    match uu____6387 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____6391 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6391
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____6397 = get_odir ()  in
    match uu____6397 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____6406 = get_cache_dir ()  in
    match uu____6406 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6410 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____6410
  
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
             let uu____6476 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____6476  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____6484 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6484 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6554 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6554 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6563  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6568  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6575  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6580  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____6585  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6591 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6597 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6603 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6609 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6616  ->
    let uu____6617 = get_codegen ()  in
    FStar_Util.map_opt uu____6617
      (fun uu___84_6621  ->
         match uu___84_6621 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6622 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6631  ->
    let uu____6632 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6632
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6649  -> let uu____6650 = get_debug ()  in uu____6650 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6660 = get_debug ()  in
    FStar_All.pipe_right uu____6660 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6677 = get_debug ()  in
       FStar_All.pipe_right uu____6677 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6686  -> let uu____6687 = get_defensive ()  in uu____6687 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6692  ->
    let uu____6693 = get_defensive ()  in uu____6693 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6700  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6705  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6710  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6715  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6721 = get_dump_module ()  in
    FStar_All.pipe_right uu____6721 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6730  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6735  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6741 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6741
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6775  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6780  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6785  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6792  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6797  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6802  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6807  ->
    let uu____6808 = get_initial_fuel ()  in
    let uu____6809 = get_max_fuel ()  in Prims.min uu____6808 uu____6809
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6814  ->
    let uu____6815 = get_initial_ifuel ()  in
    let uu____6816 = get_max_ifuel ()  in Prims.min uu____6815 uu____6816
  
let (interactive : unit -> Prims.bool) =
  fun uu____6821  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6826  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6833  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6838  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6843  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6848  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6853  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6858  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6863  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6868  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6873  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6878  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6883  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6890 = get_no_extract ()  in
    FStar_All.pipe_right uu____6890
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6901  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6906  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6911  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6918  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6923  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6928  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6933  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6938  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6943  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6948  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6953  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____6958  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____6963  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6970  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____6975  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6980  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6985  ->
    let uu____6986 = get_smtencoding_nl_arith_repr ()  in
    uu____6986 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6991  ->
    let uu____6992 = get_smtencoding_nl_arith_repr ()  in
    uu____6992 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6997  ->
    let uu____6998 = get_smtencoding_nl_arith_repr ()  in
    uu____6998 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____7003  ->
    let uu____7004 = get_smtencoding_l_arith_repr ()  in
    uu____7004 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____7009  ->
    let uu____7010 = get_smtencoding_l_arith_repr ()  in
    uu____7010 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____7015  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____7020  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____7025  -> get_tactic_trace_d () 
let (timing : unit -> Prims.bool) = fun uu____7030  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____7035  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____7040  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____7045  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____7050  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____7055  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____7060  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7067  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____7072  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____7085  ->
    let uu____7086 = get_using_facts_from ()  in
    match uu____7086 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7124  ->
    let uu____7125 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____7125
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7132  ->
    let uu____7133 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____7133 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7136 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7143  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____7148  ->
    let uu____7149 = get_smt ()  in
    match uu____7149 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7159  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____7164  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____7169  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7174  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____7179  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7184  ->
    (get_use_two_phase_tc ()) &&
      (let uu____7186 = lax ()  in Prims.op_Negation uu____7186)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7191  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7196  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7201  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7206  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7213 = get_extract ()  in
    match uu____7213 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7224 =
            let uu____7237 = get_no_extract ()  in
            let uu____7240 = get_extract_namespace ()  in
            let uu____7243 = get_extract_module ()  in
            (uu____7237, uu____7240, uu____7243)  in
          match uu____7224 with
          | ([],[],[]) -> ()
          | uu____7258 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7306,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7325 -> false  in
          let uu____7334 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7368  ->
                    match uu____7368 with
                    | (path,uu____7376) -> matches_path m_components path))
             in
          match uu____7334 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____7387,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____7407 = get_extract_namespace ()  in
          match uu____7407 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____7423 = get_extract_module ()  in
          match uu____7423 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____7435 = no_extract m1  in Prims.op_Negation uu____7435) &&
          (let uu____7437 =
             let uu____7446 = get_extract_namespace ()  in
             let uu____7449 = get_extract_module ()  in
             (uu____7446, uu____7449)  in
           (match uu____7437 with
            | ([],[]) -> true
            | uu____7460 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  