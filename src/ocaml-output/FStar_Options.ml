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
  fun uu___65_296  ->
    match uu___65_296 with
    | Bool b -> b
    | uu____298 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___66_303  ->
    match uu___66_303 with
    | Int b -> b
    | uu____305 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___67_310  ->
    match uu___67_310 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____313 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___68_320  ->
    match uu___68_320 with
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
    fun uu___69_381  ->
      match uu___69_381 with
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
  fun uu____1182  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1199  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1264 =
      let uu____1267 = peek ()  in FStar_Util.smap_try_find uu____1267 s  in
    match uu____1264 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1277 . Prims.string -> (option_val -> 'Auu____1277) -> 'Auu____1277
  = fun s  -> fun c  -> let uu____1293 = get_option s  in c uu____1293 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1298  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1305  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1312  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1319  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1326  -> lookup_opt "cache_off" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1333  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1342  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1351  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1360  -> lookup_opt "debug_level" (as_list as_string) 
let (get_defensive : unit -> Prims.string) =
  fun uu____1367  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1374  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1381  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1386  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1391  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1398  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1405  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1410  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1419  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1432  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1441  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1448  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1453  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1458  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1465  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1472  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1477  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1484  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1491  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1496  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1501  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1506  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1513  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1520  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1525  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1530  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1535  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1540  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1545  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1550  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1555  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1562  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1569  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1574  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1579  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1586  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1593  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1600  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1607  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1612  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1617  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1622  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1627  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1632  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1637  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1642  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1647  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1654  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1661  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1668  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1675  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1680  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1685  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1690  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1695  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1700  -> lookup_opt "tactic_trace_d" as_int 
let (get_timing : unit -> Prims.bool) =
  fun uu____1705  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1710  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1715  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1720  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1725  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1730  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1735  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1742  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1749  ->
    let uu____1750 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1750
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1759  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1772  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1781  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1790  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1797  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1802  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1809  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1816  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1821  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1826  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1831  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1836  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1841  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1846  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1851  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1856  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___70_1861  ->
    match uu___70_1861 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1873 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1879 = get_debug_level ()  in
    FStar_All.pipe_right uu____1879
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2012  ->
    let uu____2013 =
      let uu____2014 = FStar_ST.op_Bang _version  in
      let uu____2038 = FStar_ST.op_Bang _platform  in
      let uu____2062 = FStar_ST.op_Bang _compiler  in
      let uu____2086 = FStar_ST.op_Bang _date  in
      let uu____2110 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2014
        uu____2038 uu____2062 uu____2086 uu____2110
       in
    FStar_Util.print_string uu____2013
  
let display_usage_aux :
  'Auu____2140 'Auu____2141 .
    ('Auu____2140,Prims.string,'Auu____2141 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2189  ->
         match uu____2189 with
         | (uu____2200,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2212 =
                      let uu____2213 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2213  in
                    FStar_Util.print_string uu____2212
                  else
                    (let uu____2215 =
                       let uu____2216 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2216 doc  in
                     FStar_Util.print_string uu____2215)
              | FStar_Getopt.OneArg (uu____2217,argname) ->
                  if doc = ""
                  then
                    let uu____2225 =
                      let uu____2226 = FStar_Util.colorize_bold flag  in
                      let uu____2227 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2226 uu____2227
                       in
                    FStar_Util.print_string uu____2225
                  else
                    (let uu____2229 =
                       let uu____2230 = FStar_Util.colorize_bold flag  in
                       let uu____2231 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2230
                         uu____2231 doc
                        in
                     FStar_Util.print_string uu____2229))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2259 = o  in
    match uu____2259 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2295 =
                let uu____2296 = f ()  in set_option name uu____2296  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2311 = f x  in set_option name uu____2311
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2331 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2331  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2354 =
        let uu____2357 = lookup_opt name as_list'  in
        FStar_List.append uu____2357 [value]  in
      mk_list uu____2354
  
let accumulate_string :
  'Auu____2370 .
    Prims.string -> ('Auu____2370 -> Prims.string) -> 'Auu____2370 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2391 =
          let uu____2392 =
            let uu____2393 = post_processor value  in mk_string uu____2393
             in
          accumulated_option name uu____2392  in
        set_option name uu____2391
  
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
    match projectee with | Const _0 -> true | uu____2489 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2503 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2516 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2523 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2537 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2553 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2579 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2618 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2653 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2667 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2688 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2726 -> true
    | uu____2727 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2734 -> uu____2734
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2754 ->
              let uu____2755 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2755 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2759 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2759
          | PathStr uu____2762 -> mk_path str_val
          | SimpleStr uu____2763 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2768 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2783 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2783
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
            let uu____2802 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2802
  
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
    | PostProcessed (uu____2839,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2849,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2876 = desc_of_opt_type typ  in
      match uu____2876 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2882  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2899 =
      let uu____2900 = as_string s  in FStar_String.lowercase uu____2900  in
    mk_string uu____2899
  
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2922  ->
    let uu____2934 =
      let uu____2946 =
        let uu____2958 =
          let uu____2968 = let uu____2969 = mk_bool true  in Const uu____2969
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2968,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
           in
        let uu____2971 =
          let uu____2983 =
            let uu____2995 =
              let uu____3005 =
                let uu____3006 = mk_bool true  in Const uu____3006  in
              (FStar_Getopt.noshort, "cache_off", uu____3005,
                "Do not read or write any .checked files")
               in
            let uu____3008 =
              let uu____3020 =
                let uu____3032 =
                  let uu____3044 =
                    let uu____3056 =
                      let uu____3068 =
                        let uu____3080 =
                          let uu____3092 =
                            let uu____3102 =
                              let uu____3103 = mk_bool true  in
                              Const uu____3103  in
                            (FStar_Getopt.noshort, "detail_errors",
                              uu____3102,
                              "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                             in
                          let uu____3105 =
                            let uu____3117 =
                              let uu____3127 =
                                let uu____3128 = mk_bool true  in
                                Const uu____3128  in
                              (FStar_Getopt.noshort, "detail_hint_replay",
                                uu____3127,
                                "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                               in
                            let uu____3130 =
                              let uu____3142 =
                                let uu____3152 =
                                  let uu____3153 = mk_bool true  in
                                  Const uu____3153  in
                                (FStar_Getopt.noshort, "doc", uu____3152,
                                  "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                 in
                              let uu____3155 =
                                let uu____3167 =
                                  let uu____3179 =
                                    let uu____3189 =
                                      let uu____3190 = mk_bool true  in
                                      Const uu____3190  in
                                    (FStar_Getopt.noshort, "eager_inference",
                                      uu____3189,
                                      "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                     in
                                  let uu____3192 =
                                    let uu____3204 =
                                      let uu____3214 =
                                        let uu____3215 = mk_bool true  in
                                        Const uu____3215  in
                                      (FStar_Getopt.noshort,
                                        "eager_subtyping", uu____3214,
                                        "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                       in
                                    let uu____3217 =
                                      let uu____3229 =
                                        let uu____3241 =
                                          let uu____3253 =
                                            let uu____3265 =
                                              let uu____3275 =
                                                let uu____3276 = mk_bool true
                                                   in
                                                Const uu____3276  in
                                              (FStar_Getopt.noshort,
                                                "expose_interfaces",
                                                uu____3275,
                                                "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                               in
                                            let uu____3278 =
                                              let uu____3290 =
                                                let uu____3300 =
                                                  let uu____3301 =
                                                    mk_bool true  in
                                                  Const uu____3301  in
                                                (FStar_Getopt.noshort,
                                                  "hide_uvar_nums",
                                                  uu____3300,
                                                  "Don't print unification variable numbers")
                                                 in
                                              let uu____3303 =
                                                let uu____3315 =
                                                  let uu____3327 =
                                                    let uu____3337 =
                                                      let uu____3338 =
                                                        mk_bool true  in
                                                      Const uu____3338  in
                                                    (FStar_Getopt.noshort,
                                                      "hint_info",
                                                      uu____3337,
                                                      "Print information regarding hints (deprecated; use --query_stats instead)")
                                                     in
                                                  let uu____3340 =
                                                    let uu____3352 =
                                                      let uu____3362 =
                                                        let uu____3363 =
                                                          mk_bool true  in
                                                        Const uu____3363  in
                                                      (FStar_Getopt.noshort,
                                                        "in", uu____3362,
                                                        "Legacy interactive mode; reads input from stdin")
                                                       in
                                                    let uu____3365 =
                                                      let uu____3377 =
                                                        let uu____3387 =
                                                          let uu____3388 =
                                                            mk_bool true  in
                                                          Const uu____3388
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "ide", uu____3387,
                                                          "JSON-based interactive mode for IDEs")
                                                         in
                                                      let uu____3390 =
                                                        let uu____3402 =
                                                          let uu____3414 =
                                                            let uu____3424 =
                                                              let uu____3425
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____3425
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "indent",
                                                              uu____3424,
                                                              "Parses and outputs the files on the command line")
                                                             in
                                                          let uu____3427 =
                                                            let uu____3439 =
                                                              let uu____3451
                                                                =
                                                                let uu____3463
                                                                  =
                                                                  let uu____3473
                                                                    =
                                                                    let uu____3474
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3474
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3473,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                   in
                                                                let uu____3476
                                                                  =
                                                                  let uu____3488
                                                                    =
                                                                    let uu____3500
                                                                    =
                                                                    let uu____3510
                                                                    =
                                                                    let uu____3511
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3511
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3510,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3513
                                                                    =
                                                                    let uu____3525
                                                                    =
                                                                    let uu____3535
                                                                    =
                                                                    let uu____3536
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3536
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3535,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3538
                                                                    =
                                                                    let uu____3550
                                                                    =
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
                                                                    "MLish",
                                                                    uu____3596,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3599
                                                                    =
                                                                    let uu____3611
                                                                    =
                                                                    let uu____3623
                                                                    =
                                                                    let uu____3633
                                                                    =
                                                                    let uu____3634
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3634
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3633,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3636
                                                                    =
                                                                    let uu____3648
                                                                    =
                                                                    let uu____3660
                                                                    =
                                                                    let uu____3670
                                                                    =
                                                                    let uu____3671
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3671
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3670,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3673
                                                                    =
                                                                    let uu____3685
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
                                                                    "no_smt",
                                                                    uu____3695,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3698
                                                                    =
                                                                    let uu____3710
                                                                    =
                                                                    let uu____3720
                                                                    =
                                                                    let uu____3721
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3721
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3720,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3723
                                                                    =
                                                                    let uu____3735
                                                                    =
                                                                    let uu____3747
                                                                    =
                                                                    let uu____3759
                                                                    =
                                                                    let uu____3769
                                                                    =
                                                                    let uu____3770
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3770
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3769,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3772
                                                                    =
                                                                    let uu____3784
                                                                    =
                                                                    let uu____3794
                                                                    =
                                                                    let uu____3795
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3795
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3794,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3797
                                                                    =
                                                                    let uu____3809
                                                                    =
                                                                    let uu____3819
                                                                    =
                                                                    let uu____3820
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3820
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3819,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3822
                                                                    =
                                                                    let uu____3834
                                                                    =
                                                                    let uu____3844
                                                                    =
                                                                    let uu____3845
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3845
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3844,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3847
                                                                    =
                                                                    let uu____3859
                                                                    =
                                                                    let uu____3869
                                                                    =
                                                                    let uu____3870
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3870
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3869,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3872
                                                                    =
                                                                    let uu____3884
                                                                    =
                                                                    let uu____3894
                                                                    =
                                                                    let uu____3895
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3895
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3894,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3897
                                                                    =
                                                                    let uu____3909
                                                                    =
                                                                    let uu____3919
                                                                    =
                                                                    let uu____3920
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3920
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3919,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3922
                                                                    =
                                                                    let uu____3934
                                                                    =
                                                                    let uu____3944
                                                                    =
                                                                    let uu____3945
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3945
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3944,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3947
                                                                    =
                                                                    let uu____3959
                                                                    =
                                                                    let uu____3969
                                                                    =
                                                                    let uu____3970
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3970
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3969,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3972
                                                                    =
                                                                    let uu____3984
                                                                    =
                                                                    let uu____3996
                                                                    =
                                                                    let uu____4006
                                                                    =
                                                                    let uu____4007
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4007
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4006,
                                                                    " ")  in
                                                                    let uu____4009
                                                                    =
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
                                                                    let uu____4079
                                                                    =
                                                                    let uu____4080
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4080
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4079,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4082
                                                                    =
                                                                    let uu____4094
                                                                    =
                                                                    let uu____4104
                                                                    =
                                                                    let uu____4105
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4105
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4104,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4107
                                                                    =
                                                                    let uu____4119
                                                                    =
                                                                    let uu____4131
                                                                    =
                                                                    let uu____4141
                                                                    =
                                                                    let uu____4142
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4142
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4141,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4144
                                                                    =
                                                                    let uu____4156
                                                                    =
                                                                    let uu____4166
                                                                    =
                                                                    let uu____4167
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4167
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4166,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4169
                                                                    =
                                                                    let uu____4181
                                                                    =
                                                                    let uu____4191
                                                                    =
                                                                    let uu____4192
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4192
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4191,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4194
                                                                    =
                                                                    let uu____4206
                                                                    =
                                                                    let uu____4216
                                                                    =
                                                                    let uu____4217
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4217
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4216,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4219
                                                                    =
                                                                    let uu____4231
                                                                    =
                                                                    let uu____4241
                                                                    =
                                                                    let uu____4242
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4242
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4241,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4244
                                                                    =
                                                                    let uu____4256
                                                                    =
                                                                    let uu____4266
                                                                    =
                                                                    let uu____4267
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4267
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4266,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4269
                                                                    =
                                                                    let uu____4281
                                                                    =
                                                                    let uu____4291
                                                                    =
                                                                    let uu____4292
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4292
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4291,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4294
                                                                    =
                                                                    let uu____4306
                                                                    =
                                                                    let uu____4316
                                                                    =
                                                                    let uu____4317
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4317
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4316,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4319
                                                                    =
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
                                                                    "no_tactics",
                                                                    uu____4353,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4356
                                                                    =
                                                                    let uu____4368
                                                                    =
                                                                    let uu____4380
                                                                    =
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
                                                                    "__temp_fast_implicits",
                                                                    uu____4414,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4417
                                                                    =
                                                                    let uu____4429
                                                                    =
                                                                    let uu____4439
                                                                    =
                                                                    let uu____4440
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
                                                                    ((fun
                                                                    uu____4455
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4448)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4440
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4439,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4459
                                                                    =
                                                                    let uu____4471
                                                                    =
                                                                    let uu____4481
                                                                    =
                                                                    let uu____4482
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4482
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4481,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4484
                                                                    =
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
                                                                    "z3refresh",
                                                                    uu____4518,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4521
                                                                    =
                                                                    let uu____4533
                                                                    =
                                                                    let uu____4545
                                                                    =
                                                                    let uu____4557
                                                                    =
                                                                    let uu____4569
                                                                    =
                                                                    let uu____4581
                                                                    =
                                                                    let uu____4591
                                                                    =
                                                                    let uu____4592
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4592
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4591,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4594
                                                                    =
                                                                    let uu____4606
                                                                    =
                                                                    let uu____4616
                                                                    =
                                                                    let uu____4617
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4617
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4616,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4619
                                                                    =
                                                                    let uu____4631
                                                                    =
                                                                    let uu____4643
                                                                    =
                                                                    let uu____4655
                                                                    =
                                                                    let uu____4665
                                                                    =
                                                                    let uu____4666
                                                                    =
                                                                    let uu____4674
                                                                    =
                                                                    let uu____4675
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4675
                                                                     in
                                                                    ((fun
                                                                    uu____4681
                                                                     ->
                                                                    (
                                                                    let uu____4683
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4683);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4674)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4666
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4665,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4655]
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4643
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4631
                                                                     in
                                                                    uu____4606
                                                                    ::
                                                                    uu____4619
                                                                     in
                                                                    uu____4581
                                                                    ::
                                                                    uu____4594
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4569
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4557
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4545
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4533
                                                                     in
                                                                    uu____4508
                                                                    ::
                                                                    uu____4521
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4496
                                                                     in
                                                                    uu____4471
                                                                    ::
                                                                    uu____4484
                                                                     in
                                                                    uu____4429
                                                                    ::
                                                                    uu____4459
                                                                     in
                                                                    uu____4404
                                                                    ::
                                                                    uu____4417
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4392
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4380
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4368
                                                                     in
                                                                    uu____4343
                                                                    ::
                                                                    uu____4356
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4331
                                                                     in
                                                                    uu____4306
                                                                    ::
                                                                    uu____4319
                                                                     in
                                                                    uu____4281
                                                                    ::
                                                                    uu____4294
                                                                     in
                                                                    uu____4256
                                                                    ::
                                                                    uu____4269
                                                                     in
                                                                    uu____4231
                                                                    ::
                                                                    uu____4244
                                                                     in
                                                                    uu____4206
                                                                    ::
                                                                    uu____4219
                                                                     in
                                                                    uu____4181
                                                                    ::
                                                                    uu____4194
                                                                     in
                                                                    uu____4156
                                                                    ::
                                                                    uu____4169
                                                                     in
                                                                    uu____4131
                                                                    ::
                                                                    uu____4144
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4119
                                                                     in
                                                                    uu____4094
                                                                    ::
                                                                    uu____4107
                                                                     in
                                                                    uu____4069
                                                                    ::
                                                                    uu____4082
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4057
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4045
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4033
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4021
                                                                     in
                                                                    uu____3996
                                                                    ::
                                                                    uu____4009
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3984
                                                                     in
                                                                    uu____3959
                                                                    ::
                                                                    uu____3972
                                                                     in
                                                                    uu____3934
                                                                    ::
                                                                    uu____3947
                                                                     in
                                                                    uu____3909
                                                                    ::
                                                                    uu____3922
                                                                     in
                                                                    uu____3884
                                                                    ::
                                                                    uu____3897
                                                                     in
                                                                    uu____3859
                                                                    ::
                                                                    uu____3872
                                                                     in
                                                                    uu____3834
                                                                    ::
                                                                    uu____3847
                                                                     in
                                                                    uu____3809
                                                                    ::
                                                                    uu____3822
                                                                     in
                                                                    uu____3784
                                                                    ::
                                                                    uu____3797
                                                                     in
                                                                    uu____3759
                                                                    ::
                                                                    uu____3772
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3747
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3735
                                                                     in
                                                                    uu____3710
                                                                    ::
                                                                    uu____3723
                                                                     in
                                                                    uu____3685
                                                                    ::
                                                                    uu____3698
                                                                     in
                                                                    uu____3660
                                                                    ::
                                                                    uu____3673
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3648
                                                                     in
                                                                    uu____3623
                                                                    ::
                                                                    uu____3636
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3611
                                                                     in
                                                                    uu____3586
                                                                    ::
                                                                    uu____3599
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3574
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3562
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3550
                                                                     in
                                                                    uu____3525
                                                                    ::
                                                                    uu____3538
                                                                     in
                                                                    uu____3500
                                                                    ::
                                                                    uu____3513
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (
                                                                    ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3488
                                                                   in
                                                                uu____3463 ::
                                                                  uu____3476
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_ifuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                :: uu____3451
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "initial_fuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of recursive functions to try initially (default 2)")
                                                              :: uu____3439
                                                             in
                                                          uu____3414 ::
                                                            uu____3427
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "include",
                                                          (ReverseAccumulated
                                                             (PathStr "path")),
                                                          "A directory in which to search for files included on the command line")
                                                          :: uu____3402
                                                         in
                                                      uu____3377 ::
                                                        uu____3390
                                                       in
                                                    uu____3352 :: uu____3365
                                                     in
                                                  uu____3327 :: uu____3340
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "hint_file",
                                                  (PathStr "path"),
                                                  "Read/write hints to <path> (instead of module-specific hints files)")
                                                  :: uu____3315
                                                 in
                                              uu____3290 :: uu____3303  in
                                            uu____3265 :: uu____3278  in
                                          (FStar_Getopt.noshort,
                                            "extract_namespace",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr
                                                       "namespace name")))),
                                            "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                            :: uu____3253
                                           in
                                        (FStar_Getopt.noshort,
                                          "extract_module",
                                          (Accumulated
                                             (PostProcessed
                                                (pp_lowercase,
                                                  (SimpleStr "module_name")))),
                                          "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                          :: uu____3241
                                         in
                                      (FStar_Getopt.noshort, "extract",
                                        (Accumulated
                                           (SimpleStr
                                              "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                        "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                        :: uu____3229
                                       in
                                    uu____3204 :: uu____3217  in
                                  uu____3179 :: uu____3192  in
                                (FStar_Getopt.noshort, "dump_module",
                                  (Accumulated (SimpleStr "module_name")),
                                  "") :: uu____3167
                                 in
                              uu____3142 :: uu____3155  in
                            uu____3117 :: uu____3130  in
                          uu____3092 :: uu____3105  in
                        (FStar_Getopt.noshort, "dep",
                          (EnumStr ["make"; "graph"; "full"]),
                          "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                          :: uu____3080
                         in
                      (FStar_Getopt.noshort, "defensive",
                        (EnumStr ["no"; "warn"; "fail"]),
                        "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                        :: uu____3068
                       in
                    (FStar_Getopt.noshort, "debug_level",
                      (Accumulated
                         (OpenEnumStr
                            (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                      "Control the verbosity of debugging info") ::
                      uu____3056
                     in
                  (FStar_Getopt.noshort, "debug",
                    (Accumulated (SimpleStr "module_name")),
                    "Print lots of debugging information while checking module")
                    :: uu____3044
                   in
                (FStar_Getopt.noshort, "codegen-lib",
                  (Accumulated (SimpleStr "namespace")),
                  "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                  :: uu____3032
                 in
              (FStar_Getopt.noshort, "codegen",
                (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                "Generate code for further compilation to executable code, or build a compiler plugin")
                :: uu____3020
               in
            uu____2995 :: uu____3008  in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2983
           in
        uu____2958 :: uu____2971  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2946
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2934

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5584  ->
    let uu____5587 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5614  ->
         match uu____5614 with
         | (short,long,typ,doc) ->
             let uu____5630 =
               let uu____5642 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5642, doc)  in
             mk_spec uu____5630) uu____5587

let (settable : Prims.string -> Prims.bool) =
  fun uu___71_5652  ->
    match uu___71_5652 with
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
    | uu____5653 -> false
  
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
       (fun uu____5727  ->
          match uu____5727 with
          | (uu____5739,x,uu____5741,uu____5742) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5804  ->
          match uu____5804 with
          | (uu____5816,x,uu____5818,uu____5819) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5830  ->
    let uu____5831 = specs ()  in display_usage_aux uu____5831
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5855 -> true
    | uu____5856 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5863 -> uu____5863
  
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
          let uu____5891 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5891
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5919  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5924 =
             let uu____5927 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5927 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5924)
       in
    let uu____5984 =
      let uu____5987 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5987
       in
    (res, uu____5984)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6025  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6064 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6064 (fun x  -> ())  in
     (let uu____6070 =
        let uu____6075 =
          let uu____6076 = FStar_List.map mk_string old_verify_module  in
          List uu____6076  in
        ("verify_module", uu____6075)  in
      set_option' uu____6070);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6086 =
        let uu____6087 =
          let uu____6088 =
            let uu____6089 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6089  in
          (FStar_String.length f1) - uu____6088  in
        uu____6087 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6086  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6095 = get_lax ()  in
    if uu____6095
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6105 = module_name_of_file_name fn  in should_verify uu____6105
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6111 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6111
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6119 = should_verify m  in
    if uu____6119 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6127  ->
    let uu____6128 = get_no_default_includes ()  in
    if uu____6128
    then get_include ()
    else
      (let lib_paths =
         let uu____6135 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6135 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6144 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6144
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6158 =
         let uu____6161 = get_include ()  in
         FStar_List.append uu____6161 ["."]  in
       FStar_List.append lib_paths uu____6158)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun filename  ->
    let uu____6171 = FStar_Util.is_path_absolute filename  in
    if uu____6171
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____6178 =
         let uu____6181 = include_path ()  in FStar_List.rev uu____6181  in
       FStar_Util.find_map uu____6178
         (fun p  ->
            let path =
              if p = "." then filename else FStar_Util.join_paths p filename
               in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
  
let (prims : unit -> Prims.string) =
  fun uu____6196  ->
    let uu____6197 = get_prims ()  in
    match uu____6197 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6201 = find_file filename  in
        (match uu____6201 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6205 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6205)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6211  ->
    let uu____6212 = prims ()  in FStar_Util.basename uu____6212
  
let (pervasives : unit -> Prims.string) =
  fun uu____6217  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____6219 = find_file filename  in
    match uu____6219 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____6223 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6223
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6228  ->
    let uu____6229 = pervasives ()  in FStar_Util.basename uu____6229
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6234  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____6236 = find_file filename  in
    match uu____6236 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____6240 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6240
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____6246 = get_odir ()  in
    match uu____6246 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____6255 = get_cache_dir ()  in
    match uu____6255 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6259 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____6259
  
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
             let uu____6307 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             FStar_Ident.path_of_text uu____6307  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           let uu____6311 = FStar_Ident.path_of_text s1  in
           (uu____6311, true))
       in
    let uu____6312 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6312 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6376 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6376 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6385  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6390  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6397  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6402  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____6407  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6413 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6419 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6425 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6431 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6438  ->
    let uu____6439 = get_codegen ()  in
    FStar_Util.map_opt uu____6439
      (fun uu___72_6443  ->
         match uu___72_6443 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6444 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6453  ->
    let uu____6454 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6454
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6471  -> let uu____6472 = get_debug ()  in uu____6472 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6482 = get_debug ()  in
    FStar_All.pipe_right uu____6482 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6499 = get_debug ()  in
       FStar_All.pipe_right uu____6499 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6508  -> let uu____6509 = get_defensive ()  in uu____6509 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6514  ->
    let uu____6515 = get_defensive ()  in uu____6515 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6522  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6527  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6532  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6537  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6543 = get_dump_module ()  in
    FStar_All.pipe_right uu____6543 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6552  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6557  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6563 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6563
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6597  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6602  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6607  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6614  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6619  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6624  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6629  ->
    let uu____6630 = get_initial_fuel ()  in
    let uu____6631 = get_max_fuel ()  in Prims.min uu____6630 uu____6631
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6636  ->
    let uu____6637 = get_initial_ifuel ()  in
    let uu____6638 = get_max_ifuel ()  in Prims.min uu____6637 uu____6638
  
let (interactive : unit -> Prims.bool) =
  fun uu____6643  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6648  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6655  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6660  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6665  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6670  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6675  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6680  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6685  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6690  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6695  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6700  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6705  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6712 = get_no_extract ()  in
    FStar_All.pipe_right uu____6712
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6723  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6728  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6733  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6740  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6745  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6750  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6755  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6760  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6765  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6770  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6775  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____6780  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____6785  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6792  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____6797  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6802  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6807  ->
    let uu____6808 = get_smtencoding_nl_arith_repr ()  in
    uu____6808 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6813  ->
    let uu____6814 = get_smtencoding_nl_arith_repr ()  in
    uu____6814 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6819  ->
    let uu____6820 = get_smtencoding_nl_arith_repr ()  in
    uu____6820 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6825  ->
    let uu____6826 = get_smtencoding_l_arith_repr ()  in
    uu____6826 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6831  ->
    let uu____6832 = get_smtencoding_l_arith_repr ()  in
    uu____6832 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6837  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6842  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6847  -> get_tactic_trace_d () 
let (timing : unit -> Prims.bool) = fun uu____6852  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____6857  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____6862  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____6867  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____6872  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____6877  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____6882  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6889  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____6894  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____6905  ->
    let uu____6906 = get_using_facts_from ()  in
    match uu____6906 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____6936  ->
    let uu____6937 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____6937
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____6944  ->
    let uu____6945 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____6945 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____6948 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____6955  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____6960  ->
    let uu____6961 = get_smt ()  in
    match uu____6961 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____6971  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____6976  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____6981  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____6986  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____6991  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____6996  ->
    (get_use_two_phase_tc ()) &&
      (let uu____6998 = lax ()  in Prims.op_Negation uu____6998)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7003  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7008  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7013  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7018  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7025 = get_extract ()  in
    match uu____7025 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7036 =
            let uu____7049 = get_no_extract ()  in
            let uu____7052 = get_extract_namespace ()  in
            let uu____7055 = get_extract_module ()  in
            (uu____7049, uu____7052, uu____7055)  in
          match uu____7036 with
          | ([],[],[]) -> ()
          | uu____7070 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = FStar_Ident.path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7116,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7135 -> false  in
          let uu____7144 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7178  ->
                    match uu____7178 with
                    | (path,uu____7186) -> matches_path m_components path))
             in
          match uu____7144 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____7197,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____7217 = get_extract_namespace ()  in
          match uu____7217 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____7233 = get_extract_module ()  in
          match uu____7233 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____7245 = no_extract m1  in Prims.op_Negation uu____7245) &&
          (let uu____7247 =
             let uu____7256 = get_extract_namespace ()  in
             let uu____7259 = get_extract_module ()  in
             (uu____7256, uu____7259)  in
           (match uu____7247 with
            | ([],[]) -> true
            | uu____7270 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  