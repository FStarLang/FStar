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
  fun uu___64_296  ->
    match uu___64_296 with
    | Bool b -> b
    | uu____298 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___65_303  ->
    match uu___65_303 with
    | Int b -> b
    | uu____305 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___66_310  ->
    match uu___66_310 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____313 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___67_320  ->
    match uu___67_320 with
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
    fun uu___68_381  ->
      match uu___68_381 with
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
        let uu____518 = peek ()  in FStar_Util.smap_copy uu____518  in
      let uu____521 = FStar_ST.op_Bang fstar_options  in uu____515 ::
        uu____521
       in
    FStar_ST.op_Colon_Equals fstar_options uu____512
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____587 = FStar_ST.op_Bang fstar_options  in
    match uu____587 with
    | [] -> failwith "set on empty option stack"
    | uu____617::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
  
let (snapshot : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____656  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  -> let uu____676 = peek ()  in FStar_Util.smap_add uu____676 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____687  -> match uu____687 with | (k,v1) -> set_option k v1 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f ()  in pop (); retv) 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____734 =
      let uu____737 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____737
       in
    FStar_ST.op_Colon_Equals light_off_files uu____734
  
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
  ("dump_types_as_json", (List []));
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
  ("use_two_phase_tc", (Bool false));
  ("__no_positivity", (Bool false));
  ("__ml_no_eta_expand_coertions", (Bool false));
  ("warn_error", (String ""));
  ("use_extracted_interfaces", (Bool false))] 
let (init : unit -> unit) =
  fun uu____1188  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1205  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1274 =
      let uu____1277 = peek ()  in FStar_Util.smap_try_find uu____1277 s  in
    match uu____1274 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1287 . Prims.string -> (option_val -> 'Auu____1287) -> 'Auu____1287
  = fun s  -> fun c  -> let uu____1303 = get_option s  in c uu____1303 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1308  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1315  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1322  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1329  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1338  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1347  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1356  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1365  -> lookup_opt "debug_level" (as_list as_string) 
let (get_defensive : unit -> Prims.string) =
  fun uu____1372  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1379  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1386  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1391  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1396  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1403  -> lookup_opt "dump_module" (as_list as_string) 
let (get_dump_types_as_json : unit -> Prims.string Prims.list) =
  fun uu____1412  -> lookup_opt "dump_types_as_json" (as_list as_string) 
let (get_eager_inference : unit -> Prims.bool) =
  fun uu____1419  -> lookup_opt "eager_inference" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1424  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1433  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1446  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1455  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1462  -> lookup_opt "fs_typ_app" as_bool 
let (get_fstar_home : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1469  -> lookup_opt "fstar_home" (as_option as_string) 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1476  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1481  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1488  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1495  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1500  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1507  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1514  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1519  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1524  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1529  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1536  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1543  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1548  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1553  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1558  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1563  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1568  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1573  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1578  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1585  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1592  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1597  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1602  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1609  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1616  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1623  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1630  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1635  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1640  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1645  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1650  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1655  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1660  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1665  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1670  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1677  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1684  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1691  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1698  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1703  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1708  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1713  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1718  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1723  -> lookup_opt "tactic_trace_d" as_int 
let (get_timing : unit -> Prims.bool) =
  fun uu____1728  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1733  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1738  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1743  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1748  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1753  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1758  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1765  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1772  ->
    let uu____1773 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1773
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1782  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1795  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1804  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1813  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1820  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1825  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1832  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1839  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1844  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1849  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1854  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1859  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1864  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1869  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1874  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1879  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___69_1884  ->
    match uu___69_1884 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1896 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1902 = get_debug_level ()  in
    FStar_All.pipe_right uu____1902
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2035  ->
    let uu____2036 =
      let uu____2037 = FStar_ST.op_Bang _version  in
      let uu____2061 = FStar_ST.op_Bang _platform  in
      let uu____2085 = FStar_ST.op_Bang _compiler  in
      let uu____2109 = FStar_ST.op_Bang _date  in
      let uu____2133 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2037
        uu____2061 uu____2085 uu____2109 uu____2133
       in
    FStar_Util.print_string uu____2036
  
let display_usage_aux :
  'Auu____2163 'Auu____2164 .
    ('Auu____2163,Prims.string,'Auu____2164 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2212  ->
         match uu____2212 with
         | (uu____2223,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2235 =
                      let uu____2236 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2236  in
                    FStar_Util.print_string uu____2235
                  else
                    (let uu____2238 =
                       let uu____2239 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2239 doc  in
                     FStar_Util.print_string uu____2238)
              | FStar_Getopt.OneArg (uu____2240,argname) ->
                  if doc = ""
                  then
                    let uu____2248 =
                      let uu____2249 = FStar_Util.colorize_bold flag  in
                      let uu____2250 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2249 uu____2250
                       in
                    FStar_Util.print_string uu____2248
                  else
                    (let uu____2252 =
                       let uu____2253 = FStar_Util.colorize_bold flag  in
                       let uu____2254 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2253
                         uu____2254 doc
                        in
                     FStar_Util.print_string uu____2252))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2280 = o  in
    match uu____2280 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2313 =
                let uu____2314 = f ()  in set_option name uu____2314  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2329 = f x  in set_option name uu____2329
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2348 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2348  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2371 =
        let uu____2374 = lookup_opt name as_list'  in
        FStar_List.append uu____2374 [value]  in
      mk_list uu____2371
  
let accumulate_string :
  'Auu____2387 .
    Prims.string -> ('Auu____2387 -> Prims.string) -> 'Auu____2387 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2408 =
          let uu____2409 =
            let uu____2410 = post_processor value  in mk_string uu____2410
             in
          accumulated_option name uu____2409  in
        set_option name uu____2408
  
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
    match projectee with | Const _0 -> true | uu____2506 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2520 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2533 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2540 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2554 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2570 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2596 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2635 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2670 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2684 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2705 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2743 -> true
    | uu____2744 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2751 -> uu____2751
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2771 ->
              let uu____2772 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2772 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2776 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2776
          | PathStr uu____2779 -> mk_path str_val
          | SimpleStr uu____2780 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2785 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2800 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2800
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
            let uu____2819 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2819
  
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
    | PostProcessed (uu____2856,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2866,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2893 = desc_of_opt_type typ  in
      match uu____2893 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2899  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2916 =
      let uu____2917 = as_string s  in FStar_String.lowercase uu____2917  in
    mk_string uu____2916
  
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2938  ->
    let uu____2949 =
      let uu____2960 =
        let uu____2971 =
          let uu____2980 = let uu____2981 = mk_bool true  in Const uu____2981
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2980,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
           in
        let uu____2982 =
          let uu____2993 =
            let uu____3004 =
              let uu____3015 =
                let uu____3026 =
                  let uu____3037 =
                    let uu____3048 =
                      let uu____3059 =
                        let uu____3070 =
                          let uu____3079 =
                            let uu____3080 = mk_bool true  in
                            Const uu____3080  in
                          (FStar_Getopt.noshort, "detail_errors", uu____3079,
                            "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                           in
                        let uu____3081 =
                          let uu____3092 =
                            let uu____3101 =
                              let uu____3102 = mk_bool true  in
                              Const uu____3102  in
                            (FStar_Getopt.noshort, "detail_hint_replay",
                              uu____3101,
                              "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                             in
                          let uu____3103 =
                            let uu____3114 =
                              let uu____3123 =
                                let uu____3124 = mk_bool true  in
                                Const uu____3124  in
                              (FStar_Getopt.noshort, "doc", uu____3123,
                                "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                               in
                            let uu____3125 =
                              let uu____3136 =
                                let uu____3147 =
                                  let uu____3158 =
                                    let uu____3167 =
                                      let uu____3168 = mk_bool true  in
                                      Const uu____3168  in
                                    (FStar_Getopt.noshort, "eager_inference",
                                      uu____3167,
                                      "Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                     in
                                  let uu____3169 =
                                    let uu____3180 =
                                      let uu____3191 =
                                        let uu____3202 =
                                          let uu____3213 =
                                            let uu____3222 =
                                              let uu____3223 = mk_bool true
                                                 in
                                              Const uu____3223  in
                                            (FStar_Getopt.noshort,
                                              "expose_interfaces",
                                              uu____3222,
                                              "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                             in
                                          let uu____3224 =
                                            let uu____3235 =
                                              let uu____3246 =
                                                let uu____3255 =
                                                  let uu____3256 =
                                                    mk_bool true  in
                                                  Const uu____3256  in
                                                (FStar_Getopt.noshort,
                                                  "hide_uvar_nums",
                                                  uu____3255,
                                                  "Don't print unification variable numbers")
                                                 in
                                              let uu____3257 =
                                                let uu____3268 =
                                                  let uu____3279 =
                                                    let uu____3288 =
                                                      let uu____3289 =
                                                        mk_bool true  in
                                                      Const uu____3289  in
                                                    (FStar_Getopt.noshort,
                                                      "hint_info",
                                                      uu____3288,
                                                      "Print information regarding hints (deprecated; use --query_stats instead)")
                                                     in
                                                  let uu____3290 =
                                                    let uu____3301 =
                                                      let uu____3310 =
                                                        let uu____3311 =
                                                          mk_bool true  in
                                                        Const uu____3311  in
                                                      (FStar_Getopt.noshort,
                                                        "in", uu____3310,
                                                        "Legacy interactive mode; reads input from stdin")
                                                       in
                                                    let uu____3312 =
                                                      let uu____3323 =
                                                        let uu____3332 =
                                                          let uu____3333 =
                                                            mk_bool true  in
                                                          Const uu____3333
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "ide", uu____3332,
                                                          "JSON-based interactive mode for IDEs")
                                                         in
                                                      let uu____3334 =
                                                        let uu____3345 =
                                                          let uu____3356 =
                                                            let uu____3365 =
                                                              let uu____3366
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____3366
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "indent",
                                                              uu____3365,
                                                              "Parses and outputs the files on the command line")
                                                             in
                                                          let uu____3367 =
                                                            let uu____3378 =
                                                              let uu____3389
                                                                =
                                                                let uu____3400
                                                                  =
                                                                  let uu____3409
                                                                    =
                                                                    let uu____3410
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3410
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3409,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                   in
                                                                let uu____3411
                                                                  =
                                                                  let uu____3422
                                                                    =
                                                                    let uu____3433
                                                                    =
                                                                    let uu____3442
                                                                    =
                                                                    let uu____3443
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3443
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3442,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3444
                                                                    =
                                                                    let uu____3455
                                                                    =
                                                                    let uu____3464
                                                                    =
                                                                    let uu____3465
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3465
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3464,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3466
                                                                    =
                                                                    let uu____3477
                                                                    =
                                                                    let uu____3488
                                                                    =
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
                                                                    "MLish",
                                                                    uu____3519,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3521
                                                                    =
                                                                    let uu____3532
                                                                    =
                                                                    let uu____3543
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
                                                                    "no_default_includes",
                                                                    uu____3552,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3554
                                                                    =
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
                                                                    "no_location_info",
                                                                    uu____3585,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
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
                                                                    "no_smt",
                                                                    uu____3607,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3609
                                                                    =
                                                                    let uu____3620
                                                                    =
                                                                    let uu____3629
                                                                    =
                                                                    let uu____3630
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3630
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3629,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3631
                                                                    =
                                                                    let uu____3642
                                                                    =
                                                                    let uu____3653
                                                                    =
                                                                    let uu____3664
                                                                    =
                                                                    let uu____3673
                                                                    =
                                                                    let uu____3674
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3674
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3673,
                                                                    "Print the types of bound variables")
                                                                     in
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
                                                                    "print_effect_args",
                                                                    uu____3695,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3697
                                                                    =
                                                                    let uu____3708
                                                                    =
                                                                    let uu____3717
                                                                    =
                                                                    let uu____3718
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3718
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3717,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3719
                                                                    =
                                                                    let uu____3730
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
                                                                    "print_implicits",
                                                                    uu____3739,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3741
                                                                    =
                                                                    let uu____3752
                                                                    =
                                                                    let uu____3761
                                                                    =
                                                                    let uu____3762
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3762
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3761,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3763
                                                                    =
                                                                    let uu____3774
                                                                    =
                                                                    let uu____3783
                                                                    =
                                                                    let uu____3784
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3784
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3783,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3785
                                                                    =
                                                                    let uu____3796
                                                                    =
                                                                    let uu____3805
                                                                    =
                                                                    let uu____3806
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3806
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3805,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3807
                                                                    =
                                                                    let uu____3818
                                                                    =
                                                                    let uu____3827
                                                                    =
                                                                    let uu____3828
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3828
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3827,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3829
                                                                    =
                                                                    let uu____3840
                                                                    =
                                                                    let uu____3849
                                                                    =
                                                                    let uu____3850
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3850
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3849,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3851
                                                                    =
                                                                    let uu____3862
                                                                    =
                                                                    let uu____3873
                                                                    =
                                                                    let uu____3882
                                                                    =
                                                                    let uu____3883
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3883
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3882,
                                                                    " ")  in
                                                                    let uu____3884
                                                                    =
                                                                    let uu____3895
                                                                    =
                                                                    let uu____3906
                                                                    =
                                                                    let uu____3917
                                                                    =
                                                                    let uu____3928
                                                                    =
                                                                    let uu____3939
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
                                                                    "tactic_raw_binders",
                                                                    uu____3948,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____3950
                                                                    =
                                                                    let uu____3961
                                                                    =
                                                                    let uu____3970
                                                                    =
                                                                    let uu____3971
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3971
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3970,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____3972
                                                                    =
                                                                    let uu____3983
                                                                    =
                                                                    let uu____3994
                                                                    =
                                                                    let uu____4003
                                                                    =
                                                                    let uu____4004
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4004
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4003,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4005
                                                                    =
                                                                    let uu____4016
                                                                    =
                                                                    let uu____4025
                                                                    =
                                                                    let uu____4026
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4026
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4025,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4027
                                                                    =
                                                                    let uu____4038
                                                                    =
                                                                    let uu____4047
                                                                    =
                                                                    let uu____4048
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4048
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4047,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4049
                                                                    =
                                                                    let uu____4060
                                                                    =
                                                                    let uu____4069
                                                                    =
                                                                    let uu____4070
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4070
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4069,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4071
                                                                    =
                                                                    let uu____4082
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
                                                                    "unsafe_tactic_exec",
                                                                    uu____4091,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4093
                                                                    =
                                                                    let uu____4104
                                                                    =
                                                                    let uu____4113
                                                                    =
                                                                    let uu____4114
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4114
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4113,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4115
                                                                    =
                                                                    let uu____4126
                                                                    =
                                                                    let uu____4135
                                                                    =
                                                                    let uu____4136
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4136
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4135,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4137
                                                                    =
                                                                    let uu____4148
                                                                    =
                                                                    let uu____4157
                                                                    =
                                                                    let uu____4158
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4158
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4157,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4159
                                                                    =
                                                                    let uu____4170
                                                                    =
                                                                    let uu____4181
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
                                                                    "no_tactics",
                                                                    uu____4190,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4192
                                                                    =
                                                                    let uu____4203
                                                                    =
                                                                    let uu____4214
                                                                    =
                                                                    let uu____4225
                                                                    =
                                                                    let uu____4236
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
                                                                    "__temp_fast_implicits",
                                                                    uu____4245,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4247
                                                                    =
                                                                    let uu____4258
                                                                    =
                                                                    let uu____4268
                                                                    =
                                                                    let uu____4269
                                                                    =
                                                                    let uu____4277
                                                                    =
                                                                    let uu____4278
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4278
                                                                     in
                                                                    ((fun
                                                                    uu____4284
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4277)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4269
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4268,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4288
                                                                    =
                                                                    let uu____4300
                                                                    =
                                                                    let uu____4309
                                                                    =
                                                                    let uu____4310
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4310
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4309,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4311
                                                                    =
                                                                    let uu____4322
                                                                    =
                                                                    let uu____4333
                                                                    =
                                                                    let uu____4342
                                                                    =
                                                                    let uu____4343
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4343
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4342,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4344
                                                                    =
                                                                    let uu____4355
                                                                    =
                                                                    let uu____4366
                                                                    =
                                                                    let uu____4377
                                                                    =
                                                                    let uu____4388
                                                                    =
                                                                    let uu____4399
                                                                    =
                                                                    let uu____4408
                                                                    =
                                                                    let uu____4409
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4409
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4408,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4410
                                                                    =
                                                                    let uu____4421
                                                                    =
                                                                    let uu____4430
                                                                    =
                                                                    let uu____4431
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4431
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4430,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4432
                                                                    =
                                                                    let uu____4443
                                                                    =
                                                                    let uu____4454
                                                                    =
                                                                    let uu____4463
                                                                    =
                                                                    let uu____4464
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4464
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    uu____4463,
                                                                    "Extract interfaces from the dependencies and use them for verification")
                                                                     in
                                                                    let uu____4465
                                                                    =
                                                                    let uu____4476
                                                                    =
                                                                    let uu____4486
                                                                    =
                                                                    let uu____4487
                                                                    =
                                                                    let uu____4495
                                                                    =
                                                                    let uu____4496
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4496
                                                                     in
                                                                    ((fun
                                                                    uu____4502
                                                                     ->
                                                                    (
                                                                    let uu____4504
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4504);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4495)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4487
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4486,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4476]
                                                                     in
                                                                    uu____4454
                                                                    ::
                                                                    uu____4465
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4443
                                                                     in
                                                                    uu____4421
                                                                    ::
                                                                    uu____4432
                                                                     in
                                                                    uu____4399
                                                                    ::
                                                                    uu____4410
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'false')")
                                                                    ::
                                                                    uu____4388
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4377
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4366
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4355
                                                                     in
                                                                    uu____4333
                                                                    ::
                                                                    uu____4344
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4322
                                                                     in
                                                                    uu____4300
                                                                    ::
                                                                    uu____4311
                                                                     in
                                                                    uu____4258
                                                                    ::
                                                                    uu____4288
                                                                     in
                                                                    uu____4236
                                                                    ::
                                                                    uu____4247
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4225
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4214
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4203
                                                                     in
                                                                    uu____4181
                                                                    ::
                                                                    uu____4192
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4170
                                                                     in
                                                                    uu____4148
                                                                    ::
                                                                    uu____4159
                                                                     in
                                                                    uu____4126
                                                                    ::
                                                                    uu____4137
                                                                     in
                                                                    uu____4104
                                                                    ::
                                                                    uu____4115
                                                                     in
                                                                    uu____4082
                                                                    ::
                                                                    uu____4093
                                                                     in
                                                                    uu____4060
                                                                    ::
                                                                    uu____4071
                                                                     in
                                                                    uu____4038
                                                                    ::
                                                                    uu____4049
                                                                     in
                                                                    uu____4016
                                                                    ::
                                                                    uu____4027
                                                                     in
                                                                    uu____3994
                                                                    ::
                                                                    uu____4005
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3983
                                                                     in
                                                                    uu____3961
                                                                    ::
                                                                    uu____3972
                                                                     in
                                                                    uu____3939
                                                                    ::
                                                                    uu____3950
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3928
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3917
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3906
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3895
                                                                     in
                                                                    uu____3873
                                                                    ::
                                                                    uu____3884
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3862
                                                                     in
                                                                    uu____3840
                                                                    ::
                                                                    uu____3851
                                                                     in
                                                                    uu____3818
                                                                    ::
                                                                    uu____3829
                                                                     in
                                                                    uu____3796
                                                                    ::
                                                                    uu____3807
                                                                     in
                                                                    uu____3774
                                                                    ::
                                                                    uu____3785
                                                                     in
                                                                    uu____3752
                                                                    ::
                                                                    uu____3763
                                                                     in
                                                                    uu____3730
                                                                    ::
                                                                    uu____3741
                                                                     in
                                                                    uu____3708
                                                                    ::
                                                                    uu____3719
                                                                     in
                                                                    uu____3686
                                                                    ::
                                                                    uu____3697
                                                                     in
                                                                    uu____3664
                                                                    ::
                                                                    uu____3675
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3653
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3642
                                                                     in
                                                                    uu____3620
                                                                    ::
                                                                    uu____3631
                                                                     in
                                                                    uu____3598
                                                                    ::
                                                                    uu____3609
                                                                     in
                                                                    uu____3576
                                                                    ::
                                                                    uu____3587
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3565
                                                                     in
                                                                    uu____3543
                                                                    ::
                                                                    uu____3554
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3532
                                                                     in
                                                                    uu____3510
                                                                    ::
                                                                    uu____3521
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3499
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3488
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3477
                                                                     in
                                                                    uu____3455
                                                                    ::
                                                                    uu____3466
                                                                     in
                                                                    uu____3433
                                                                    ::
                                                                    uu____3444
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (
                                                                    ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3422
                                                                   in
                                                                uu____3400 ::
                                                                  uu____3411
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_ifuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                :: uu____3389
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "initial_fuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of recursive functions to try initially (default 2)")
                                                              :: uu____3378
                                                             in
                                                          uu____3356 ::
                                                            uu____3367
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "include",
                                                          (ReverseAccumulated
                                                             (PathStr "path")),
                                                          "A directory in which to search for files included on the command line")
                                                          :: uu____3345
                                                         in
                                                      uu____3323 ::
                                                        uu____3334
                                                       in
                                                    uu____3301 :: uu____3312
                                                     in
                                                  uu____3279 :: uu____3290
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "hint_file",
                                                  (PathStr "path"),
                                                  "Read/write hints to <path> (instead of module-specific hints files)")
                                                  :: uu____3268
                                                 in
                                              uu____3246 :: uu____3257  in
                                            (FStar_Getopt.noshort,
                                              "fstar_home", (PathStr "dir"),
                                              "Set the FSTAR_HOME variable to <dir>")
                                              :: uu____3235
                                             in
                                          uu____3213 :: uu____3224  in
                                        (FStar_Getopt.noshort,
                                          "extract_namespace",
                                          (Accumulated
                                             (PostProcessed
                                                (pp_lowercase,
                                                  (SimpleStr "namespace name")))),
                                          "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                          :: uu____3202
                                         in
                                      (FStar_Getopt.noshort,
                                        "extract_module",
                                        (Accumulated
                                           (PostProcessed
                                              (pp_lowercase,
                                                (SimpleStr "module_name")))),
                                        "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                        :: uu____3191
                                       in
                                    (FStar_Getopt.noshort, "extract",
                                      (Accumulated
                                         (SimpleStr
                                            "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                      "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                      :: uu____3180
                                     in
                                  uu____3158 :: uu____3169  in
                                (FStar_Getopt.noshort, "dump_types_as_json",
                                  (Accumulated (SimpleStr "module_name")),
                                  "Print the types of top-level symbols in a module as json")
                                  :: uu____3147
                                 in
                              (FStar_Getopt.noshort, "dump_module",
                                (Accumulated (SimpleStr "module_name")),
                                "Print a module after desugaring and after type-checking")
                                :: uu____3136
                               in
                            uu____3114 :: uu____3125  in
                          uu____3092 :: uu____3103  in
                        uu____3070 :: uu____3081  in
                      (FStar_Getopt.noshort, "dep",
                        (EnumStr ["make"; "graph"; "full"]),
                        "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                        :: uu____3059
                       in
                    (FStar_Getopt.noshort, "defensive",
                      (EnumStr ["no"; "warn"; "fail"]),
                      "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                      :: uu____3048
                     in
                  (FStar_Getopt.noshort, "debug_level",
                    (Accumulated
                       (OpenEnumStr
                          (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                    "Control the verbosity of debugging info") :: uu____3037
                   in
                (FStar_Getopt.noshort, "debug",
                  (Accumulated (SimpleStr "module_name")),
                  "Print lots of debugging information while checking module")
                  :: uu____3026
                 in
              (FStar_Getopt.noshort, "codegen-lib",
                (Accumulated (SimpleStr "namespace")),
                "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                :: uu____3015
               in
            (FStar_Getopt.noshort, "codegen",
              (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
              "Generate code for further compilation to executable code, or build a compiler plugin")
              :: uu____3004
             in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2993
           in
        uu____2971 :: uu____2982  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2960
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2949

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5272  ->
    let uu____5275 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5300  ->
         match uu____5300 with
         | (short,long,typ,doc) ->
             let uu____5313 =
               let uu____5324 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5324, doc)  in
             mk_spec uu____5313) uu____5275

let (settable : Prims.string -> Prims.bool) =
  fun uu___70_5333  ->
    match uu___70_5333 with
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
    | uu____5334 -> false
  
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
       (fun uu____5393  ->
          match uu____5393 with
          | (uu____5404,x,uu____5406,uu____5407) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5453  ->
          match uu____5453 with
          | (uu____5464,x,uu____5466,uu____5467) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5476  ->
    let uu____5477 = specs ()  in display_usage_aux uu____5477
  
let (fstar_home : unit -> Prims.string) =
  fun uu____5494  ->
    let uu____5495 = get_fstar_home ()  in
    match uu____5495 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir ()  in
        let x1 = Prims.strcat x "/.."  in
        ((let uu____5501 =
            let uu____5506 = mk_string x1  in ("fstar_home", uu____5506)  in
          set_option' uu____5501);
         x1)
    | FStar_Pervasives_Native.Some x -> x
  
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5517 -> true
    | uu____5518 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5525 -> uu____5525
  
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
          let uu____5573 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5573
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5601  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5606 =
             let uu____5609 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5609 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5606)
       in
    let uu____5666 =
      let uu____5669 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5669
       in
    (res, uu____5666)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____5707  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____5746 = specs ()  in
       FStar_Getopt.parse_cmdline uu____5746 (fun x  -> ())  in
     (let uu____5752 =
        let uu____5757 =
          let uu____5758 = FStar_List.map mk_string old_verify_module  in
          List uu____5758  in
        ("verify_module", uu____5757)  in
      set_option' uu____5752);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____5768 =
        let uu____5769 =
          let uu____5770 =
            let uu____5771 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____5771  in
          (FStar_String.length f1) - uu____5770  in
        uu____5769 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5768  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5777 = get_lax ()  in
    if uu____5777
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____5787 = module_name_of_file_name fn  in should_verify uu____5787
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5793 = get___temp_no_proj ()  in
    FStar_List.contains m uu____5793
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5801 = should_verify m  in
    if uu____5801 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____5809  ->
    let uu____5810 = get_no_default_includes ()  in
    if uu____5810
    then get_include ()
    else
      (let h = fstar_home ()  in
       let defs = universe_include_path_base_dirs  in
       let uu____5818 =
         let uu____5821 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x))
            in
         FStar_All.pipe_right uu____5821
           (FStar_List.filter FStar_Util.file_exists)
          in
       let uu____5834 =
         let uu____5837 = get_include ()  in
         FStar_List.append uu____5837 ["."]  in
       FStar_List.append uu____5818 uu____5834)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun filename  ->
    let uu____5847 = FStar_Util.is_path_absolute filename  in
    if uu____5847
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5854 =
         let uu____5857 = include_path ()  in FStar_List.rev uu____5857  in
       FStar_Util.find_map uu____5854
         (fun p  ->
            let path =
              if p = "." then filename else FStar_Util.join_paths p filename
               in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
  
let (prims : unit -> Prims.string) =
  fun uu____5872  ->
    let uu____5873 = get_prims ()  in
    match uu____5873 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____5877 = find_file filename  in
        (match uu____5877 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5881 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____5881)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____5887  ->
    let uu____5888 = prims ()  in FStar_Util.basename uu____5888
  
let (pervasives : unit -> Prims.string) =
  fun uu____5893  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____5895 = find_file filename  in
    match uu____5895 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5899 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5899
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____5904  ->
    let uu____5905 = pervasives ()  in FStar_Util.basename uu____5905
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____5910  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____5912 = find_file filename  in
    match uu____5912 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5916 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5916
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____5922 = get_odir ()  in
    match uu____5922 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____5931 = get_cache_dir ()  in
    match uu____5931 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____5935 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____5935
  
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
             let uu____5989 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             FStar_Ident.path_of_text uu____5989  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           let uu____5993 = FStar_Ident.path_of_text s1  in
           (uu____5993, true))
       in
    let uu____5994 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____5994 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6064 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6064 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6073  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6078  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6085  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6090  -> get_cache_checked_modules () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6096 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6102 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6108 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6114 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6121  ->
    let uu____6122 = get_codegen ()  in
    FStar_Util.map_opt uu____6122
      (fun uu___71_6126  ->
         match uu___71_6126 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6127 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6136  ->
    let uu____6137 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6137
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6154  -> let uu____6155 = get_debug ()  in uu____6155 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6165 = get_debug ()  in
    FStar_All.pipe_right uu____6165 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6182 = get_debug ()  in
       FStar_All.pipe_right uu____6182 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6191  -> let uu____6192 = get_defensive ()  in uu____6192 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6197  ->
    let uu____6198 = get_defensive ()  in uu____6198 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6205  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6210  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6215  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6220  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6226 = get_dump_module ()  in
    FStar_All.pipe_right uu____6226 (FStar_List.contains s)
  
let (dump_types_as_json : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6236 = get_dump_types_as_json ()  in
    FStar_All.pipe_right uu____6236 (FStar_List.contains s)
  
let (eager_inference : unit -> Prims.bool) =
  fun uu____6245  -> get_eager_inference () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6250  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6256 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6256
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6290  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6295  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6300  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6307  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6312  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6317  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6322  ->
    let uu____6323 = get_initial_fuel ()  in
    let uu____6324 = get_max_fuel ()  in Prims.min uu____6323 uu____6324
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6329  ->
    let uu____6330 = get_initial_ifuel ()  in
    let uu____6331 = get_max_ifuel ()  in Prims.min uu____6330 uu____6331
  
let (interactive : unit -> Prims.bool) =
  fun uu____6336  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6341  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6348  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6353  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6358  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6363  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6368  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6373  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6378  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6383  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6388  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6393  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6398  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6405 = get_no_extract ()  in
    FStar_All.pipe_right uu____6405
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6416  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6421  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6426  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6433  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6438  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6443  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6448  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6453  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6458  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6463  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6468  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____6473  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____6478  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6485  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____6490  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6495  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6500  ->
    let uu____6501 = get_smtencoding_nl_arith_repr ()  in
    uu____6501 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6506  ->
    let uu____6507 = get_smtencoding_nl_arith_repr ()  in
    uu____6507 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6512  ->
    let uu____6513 = get_smtencoding_nl_arith_repr ()  in
    uu____6513 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6518  ->
    let uu____6519 = get_smtencoding_l_arith_repr ()  in
    uu____6519 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6524  ->
    let uu____6525 = get_smtencoding_l_arith_repr ()  in
    uu____6525 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6530  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6535  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6540  -> get_tactic_trace_d () 
let (timing : unit -> Prims.bool) = fun uu____6545  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____6550  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____6555  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____6560  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____6565  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____6570  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____6575  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6582  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____6587  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____6598  ->
    let uu____6599 = get_using_facts_from ()  in
    match uu____6599 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____6635  ->
    let uu____6636 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____6636
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____6643  ->
    let uu____6644 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____6644 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____6647 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____6654  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____6659  ->
    let uu____6660 = get_smt ()  in
    match uu____6660 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____6670  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____6675  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____6680  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____6685  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____6690  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____6695  -> get_use_two_phase_tc () 
let (no_positivity : unit -> Prims.bool) =
  fun uu____6700  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____6705  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____6710  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____6715  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____6722 = get_extract ()  in
    match uu____6722 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____6733 =
            let uu____6746 = get_no_extract ()  in
            let uu____6749 = get_extract_namespace ()  in
            let uu____6752 = get_extract_module ()  in
            (uu____6746, uu____6749, uu____6752)  in
          match uu____6733 with
          | ([],[],[]) -> ()
          | uu____6767 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = FStar_Ident.path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____6813,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____6832 -> false  in
          let uu____6841 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____6875  ->
                    match uu____6875 with
                    | (path,uu____6883) -> matches_path m_components path))
             in
          match uu____6841 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____6894,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____6914 = get_extract_namespace ()  in
          match uu____6914 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____6930 = get_extract_module ()  in
          match uu____6930 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____6942 = no_extract m1  in Prims.op_Negation uu____6942) &&
          (let uu____6944 =
             let uu____6953 = get_extract_namespace ()  in
             let uu____6956 = get_extract_module ()  in
             (uu____6953, uu____6956)  in
           (match uu____6944 with
            | ([],[]) -> true
            | uu____6967 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  