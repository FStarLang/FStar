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
  ("warn_error", (String ""));
  ("use_extracted_interfaces", (Bool false))] 
let (init : unit -> unit) =
  fun uu____1170  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1187  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1244 =
      let uu____1247 = peek ()  in FStar_Util.smap_try_find uu____1247 s  in
    match uu____1244 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1257 . Prims.string -> (option_val -> 'Auu____1257) -> 'Auu____1257
  = fun s  -> fun c  -> let uu____1273 = get_option s  in c uu____1273 
let (get_abort_on : unit -> Prims.int) =
  fun uu____1278  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1283  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1290  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1297  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1304  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1311  -> lookup_opt "cache_off" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1318  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1327  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1336  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1345  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____1352  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1359  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1366  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1371  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1376  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1383  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1390  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1395  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1404  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1417  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1426  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1433  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1438  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1443  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1450  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1457  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1462  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1469  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1476  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1481  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1486  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1491  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1498  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1505  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1510  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1515  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1520  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1525  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1530  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1535  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1540  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1547  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1554  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1559  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1564  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1571  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1578  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1585  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1592  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1597  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1602  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1607  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1612  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1617  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1622  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1627  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1632  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1639  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1646  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1653  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1660  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1665  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1670  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1675  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1680  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1685  -> lookup_opt "tactic_trace_d" as_int 
let (get_timing : unit -> Prims.bool) =
  fun uu____1690  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1695  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1700  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1705  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1710  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1715  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1720  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1727  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1734  ->
    let uu____1735 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1735
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1744  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1757  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1766  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1775  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1782  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1787  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1794  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1801  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1806  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1811  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1816  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1821  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1826  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1831  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1836  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1841  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___81_1846  ->
    match uu___81_1846 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1858 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1864 = get_debug_level ()  in
    FStar_All.pipe_right uu____1864
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____1997  ->
    let uu____1998 =
      let uu____1999 = FStar_ST.op_Bang _version  in
      let uu____2019 = FStar_ST.op_Bang _platform  in
      let uu____2039 = FStar_ST.op_Bang _compiler  in
      let uu____2059 = FStar_ST.op_Bang _date  in
      let uu____2079 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1999
        uu____2019 uu____2039 uu____2059 uu____2079
       in
    FStar_Util.print_string uu____1998
  
let display_usage_aux :
  'Auu____2105 'Auu____2106 .
    ('Auu____2105,Prims.string,'Auu____2106 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2154  ->
         match uu____2154 with
         | (uu____2165,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2177 =
                      let uu____2178 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2178  in
                    FStar_Util.print_string uu____2177
                  else
                    (let uu____2180 =
                       let uu____2181 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2181 doc  in
                     FStar_Util.print_string uu____2180)
              | FStar_Getopt.OneArg (uu____2182,argname) ->
                  if doc = ""
                  then
                    let uu____2190 =
                      let uu____2191 = FStar_Util.colorize_bold flag  in
                      let uu____2192 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2191 uu____2192
                       in
                    FStar_Util.print_string uu____2190
                  else
                    (let uu____2194 =
                       let uu____2195 = FStar_Util.colorize_bold flag  in
                       let uu____2196 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2195
                         uu____2196 doc
                        in
                     FStar_Util.print_string uu____2194))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2224 = o  in
    match uu____2224 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2260 =
                let uu____2261 = f ()  in set_option name uu____2261  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2276 = f x  in set_option name uu____2276
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2296 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2296  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2319 =
        let uu____2322 = lookup_opt name as_list'  in
        FStar_List.append uu____2322 [value]  in
      mk_list uu____2319
  
let accumulate_string :
  'Auu____2335 .
    Prims.string -> ('Auu____2335 -> Prims.string) -> 'Auu____2335 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2356 =
          let uu____2357 =
            let uu____2358 = post_processor value  in mk_string uu____2358
             in
          accumulated_option name uu____2357  in
        set_option name uu____2356
  
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
    match projectee with | Const _0 -> true | uu____2454 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2468 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2481 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2488 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2502 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2518 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2544 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2583 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2618 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2632 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2653 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2691 -> true
    | uu____2692 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2699 -> uu____2699
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2719 ->
              let uu____2720 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2720 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2724 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2724
          | PathStr uu____2727 -> mk_path str_val
          | SimpleStr uu____2728 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2733 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2748 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2748
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
            let uu____2767 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2767
  
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
    | PostProcessed (uu____2804,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2814,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2841 = desc_of_opt_type typ  in
      match uu____2841 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2847  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2864 =
      let uu____2865 = as_string s  in FStar_String.lowercase uu____2865  in
    mk_string uu____2864
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2913  ->
    let uu____2925 =
      let uu____2937 =
        let uu____2949 =
          let uu____2961 =
            let uu____2971 =
              let uu____2972 = mk_bool true  in Const uu____2972  in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____2971,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
             in
          let uu____2974 =
            let uu____2986 =
              let uu____2998 =
                let uu____3008 =
                  let uu____3009 = mk_bool true  in Const uu____3009  in
                (FStar_Getopt.noshort, "cache_off", uu____3008,
                  "Do not read or write any .checked files")
                 in
              let uu____3011 =
                let uu____3023 =
                  let uu____3035 =
                    let uu____3047 =
                      let uu____3059 =
                        let uu____3071 =
                          let uu____3083 =
                            let uu____3095 =
                              let uu____3105 =
                                let uu____3106 = mk_bool true  in
                                Const uu____3106  in
                              (FStar_Getopt.noshort, "detail_errors",
                                uu____3105,
                                "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                               in
                            let uu____3108 =
                              let uu____3120 =
                                let uu____3130 =
                                  let uu____3131 = mk_bool true  in
                                  Const uu____3131  in
                                (FStar_Getopt.noshort, "detail_hint_replay",
                                  uu____3130,
                                  "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                 in
                              let uu____3133 =
                                let uu____3145 =
                                  let uu____3155 =
                                    let uu____3156 = mk_bool true  in
                                    Const uu____3156  in
                                  (FStar_Getopt.noshort, "doc", uu____3155,
                                    "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                   in
                                let uu____3158 =
                                  let uu____3170 =
                                    let uu____3182 =
                                      let uu____3192 =
                                        let uu____3193 = mk_bool true  in
                                        Const uu____3193  in
                                      (FStar_Getopt.noshort,
                                        "eager_inference", uu____3192,
                                        "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                       in
                                    let uu____3195 =
                                      let uu____3207 =
                                        let uu____3217 =
                                          let uu____3218 = mk_bool true  in
                                          Const uu____3218  in
                                        (FStar_Getopt.noshort,
                                          "eager_subtyping", uu____3217,
                                          "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                         in
                                      let uu____3220 =
                                        let uu____3232 =
                                          let uu____3244 =
                                            let uu____3256 =
                                              let uu____3268 =
                                                let uu____3278 =
                                                  let uu____3279 =
                                                    mk_bool true  in
                                                  Const uu____3279  in
                                                (FStar_Getopt.noshort,
                                                  "expose_interfaces",
                                                  uu____3278,
                                                  "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                 in
                                              let uu____3281 =
                                                let uu____3293 =
                                                  let uu____3303 =
                                                    let uu____3304 =
                                                      mk_bool true  in
                                                    Const uu____3304  in
                                                  (FStar_Getopt.noshort,
                                                    "hide_uvar_nums",
                                                    uu____3303,
                                                    "Don't print unification variable numbers")
                                                   in
                                                let uu____3306 =
                                                  let uu____3318 =
                                                    let uu____3330 =
                                                      let uu____3340 =
                                                        let uu____3341 =
                                                          mk_bool true  in
                                                        Const uu____3341  in
                                                      (FStar_Getopt.noshort,
                                                        "hint_info",
                                                        uu____3340,
                                                        "Print information regarding hints (deprecated; use --query_stats instead)")
                                                       in
                                                    let uu____3343 =
                                                      let uu____3355 =
                                                        let uu____3365 =
                                                          let uu____3366 =
                                                            mk_bool true  in
                                                          Const uu____3366
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "in", uu____3365,
                                                          "Legacy interactive mode; reads input from stdin")
                                                         in
                                                      let uu____3368 =
                                                        let uu____3380 =
                                                          let uu____3390 =
                                                            let uu____3391 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3391
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "ide",
                                                            uu____3390,
                                                            "JSON-based interactive mode for IDEs")
                                                           in
                                                        let uu____3393 =
                                                          let uu____3405 =
                                                            let uu____3417 =
                                                              let uu____3427
                                                                =
                                                                let uu____3428
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____3428
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "indent",
                                                                uu____3427,
                                                                "Parses and outputs the files on the command line")
                                                               in
                                                            let uu____3430 =
                                                              let uu____3442
                                                                =
                                                                let uu____3454
                                                                  =
                                                                  let uu____3466
                                                                    =
                                                                    let uu____3476
                                                                    =
                                                                    let uu____3477
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3477
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3476,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                  let uu____3479
                                                                    =
                                                                    let uu____3491
                                                                    =
                                                                    let uu____3503
                                                                    =
                                                                    let uu____3513
                                                                    =
                                                                    let uu____3514
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3514
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3513,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3516
                                                                    =
                                                                    let uu____3528
                                                                    =
                                                                    let uu____3538
                                                                    =
                                                                    let uu____3539
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3539
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3538,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3541
                                                                    =
                                                                    let uu____3553
                                                                    =
                                                                    let uu____3565
                                                                    =
                                                                    let uu____3577
                                                                    =
                                                                    let uu____3589
                                                                    =
                                                                    let uu____3599
                                                                    =
                                                                    let uu____3600
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3600
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3599,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3602
                                                                    =
                                                                    let uu____3614
                                                                    =
                                                                    let uu____3626
                                                                    =
                                                                    let uu____3636
                                                                    =
                                                                    let uu____3637
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3637
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3636,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3639
                                                                    =
                                                                    let uu____3651
                                                                    =
                                                                    let uu____3663
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
                                                                    "no_location_info",
                                                                    uu____3673,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3676
                                                                    =
                                                                    let uu____3688
                                                                    =
                                                                    let uu____3698
                                                                    =
                                                                    let uu____3699
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3699
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3698,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3701
                                                                    =
                                                                    let uu____3713
                                                                    =
                                                                    let uu____3723
                                                                    =
                                                                    let uu____3724
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3724
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3723,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3726
                                                                    =
                                                                    let uu____3738
                                                                    =
                                                                    let uu____3750
                                                                    =
                                                                    let uu____3762
                                                                    =
                                                                    let uu____3772
                                                                    =
                                                                    let uu____3773
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3773
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3772,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3775
                                                                    =
                                                                    let uu____3787
                                                                    =
                                                                    let uu____3797
                                                                    =
                                                                    let uu____3798
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3798
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3797,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3800
                                                                    =
                                                                    let uu____3812
                                                                    =
                                                                    let uu____3822
                                                                    =
                                                                    let uu____3823
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3823
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3822,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3825
                                                                    =
                                                                    let uu____3837
                                                                    =
                                                                    let uu____3847
                                                                    =
                                                                    let uu____3848
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3848
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3847,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3850
                                                                    =
                                                                    let uu____3862
                                                                    =
                                                                    let uu____3872
                                                                    =
                                                                    let uu____3873
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3873
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3872,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3875
                                                                    =
                                                                    let uu____3887
                                                                    =
                                                                    let uu____3897
                                                                    =
                                                                    let uu____3898
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3898
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3897,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3900
                                                                    =
                                                                    let uu____3912
                                                                    =
                                                                    let uu____3922
                                                                    =
                                                                    let uu____3923
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3923
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3922,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3925
                                                                    =
                                                                    let uu____3937
                                                                    =
                                                                    let uu____3947
                                                                    =
                                                                    let uu____3948
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3948
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3947,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3950
                                                                    =
                                                                    let uu____3962
                                                                    =
                                                                    let uu____3972
                                                                    =
                                                                    let uu____3973
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3973
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3972,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3975
                                                                    =
                                                                    let uu____3987
                                                                    =
                                                                    let uu____3999
                                                                    =
                                                                    let uu____4009
                                                                    =
                                                                    let uu____4010
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4010
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4009,
                                                                    " ")  in
                                                                    let uu____4012
                                                                    =
                                                                    let uu____4024
                                                                    =
                                                                    let uu____4036
                                                                    =
                                                                    let uu____4048
                                                                    =
                                                                    let uu____4060
                                                                    =
                                                                    let uu____4072
                                                                    =
                                                                    let uu____4082
                                                                    =
                                                                    let uu____4083
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4083
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4082,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4085
                                                                    =
                                                                    let uu____4097
                                                                    =
                                                                    let uu____4107
                                                                    =
                                                                    let uu____4108
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4108
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4107,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4110
                                                                    =
                                                                    let uu____4122
                                                                    =
                                                                    let uu____4134
                                                                    =
                                                                    let uu____4144
                                                                    =
                                                                    let uu____4145
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4145
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4144,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4147
                                                                    =
                                                                    let uu____4159
                                                                    =
                                                                    let uu____4169
                                                                    =
                                                                    let uu____4170
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4170
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4169,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4172
                                                                    =
                                                                    let uu____4184
                                                                    =
                                                                    let uu____4194
                                                                    =
                                                                    let uu____4195
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4195
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4194,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4197
                                                                    =
                                                                    let uu____4209
                                                                    =
                                                                    let uu____4219
                                                                    =
                                                                    let uu____4220
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4220
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4219,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4222
                                                                    =
                                                                    let uu____4234
                                                                    =
                                                                    let uu____4244
                                                                    =
                                                                    let uu____4245
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4245
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4244,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4247
                                                                    =
                                                                    let uu____4259
                                                                    =
                                                                    let uu____4269
                                                                    =
                                                                    let uu____4270
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4270
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4269,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4272
                                                                    =
                                                                    let uu____4284
                                                                    =
                                                                    let uu____4294
                                                                    =
                                                                    let uu____4295
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4295
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4294,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4297
                                                                    =
                                                                    let uu____4309
                                                                    =
                                                                    let uu____4319
                                                                    =
                                                                    let uu____4320
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4320
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4319,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4322
                                                                    =
                                                                    let uu____4334
                                                                    =
                                                                    let uu____4346
                                                                    =
                                                                    let uu____4356
                                                                    =
                                                                    let uu____4357
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4357
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4356,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4359
                                                                    =
                                                                    let uu____4371
                                                                    =
                                                                    let uu____4383
                                                                    =
                                                                    let uu____4395
                                                                    =
                                                                    let uu____4407
                                                                    =
                                                                    let uu____4417
                                                                    =
                                                                    let uu____4418
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4418
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4417,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4420
                                                                    =
                                                                    let uu____4432
                                                                    =
                                                                    let uu____4442
                                                                    =
                                                                    let uu____4443
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
                                                                    ((fun
                                                                    uu____4458
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4451)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4443
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4442,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4462
                                                                    =
                                                                    let uu____4474
                                                                    =
                                                                    let uu____4484
                                                                    =
                                                                    let uu____4485
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4485
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4484,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4487
                                                                    =
                                                                    let uu____4499
                                                                    =
                                                                    let uu____4511
                                                                    =
                                                                    let uu____4521
                                                                    =
                                                                    let uu____4522
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4522
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4521,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4524
                                                                    =
                                                                    let uu____4536
                                                                    =
                                                                    let uu____4548
                                                                    =
                                                                    let uu____4560
                                                                    =
                                                                    let uu____4572
                                                                    =
                                                                    let uu____4584
                                                                    =
                                                                    let uu____4594
                                                                    =
                                                                    let uu____4595
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4595
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4594,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4597
                                                                    =
                                                                    let uu____4609
                                                                    =
                                                                    let uu____4619
                                                                    =
                                                                    let uu____4620
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4620
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4619,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4622
                                                                    =
                                                                    let uu____4634
                                                                    =
                                                                    let uu____4646
                                                                    =
                                                                    let uu____4658
                                                                    =
                                                                    let uu____4668
                                                                    =
                                                                    let uu____4669
                                                                    =
                                                                    let uu____4677
                                                                    =
                                                                    let uu____4678
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4678
                                                                     in
                                                                    ((fun
                                                                    uu____4684
                                                                     ->
                                                                    (
                                                                    let uu____4686
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4686);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4677)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4669
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4668,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4658]
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4646
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4634
                                                                     in
                                                                    uu____4609
                                                                    ::
                                                                    uu____4622
                                                                     in
                                                                    uu____4584
                                                                    ::
                                                                    uu____4597
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4572
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4560
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4548
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4536
                                                                     in
                                                                    uu____4511
                                                                    ::
                                                                    uu____4524
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4499
                                                                     in
                                                                    uu____4474
                                                                    ::
                                                                    uu____4487
                                                                     in
                                                                    uu____4432
                                                                    ::
                                                                    uu____4462
                                                                     in
                                                                    uu____4407
                                                                    ::
                                                                    uu____4420
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4395
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4383
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4371
                                                                     in
                                                                    uu____4346
                                                                    ::
                                                                    uu____4359
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4334
                                                                     in
                                                                    uu____4309
                                                                    ::
                                                                    uu____4322
                                                                     in
                                                                    uu____4284
                                                                    ::
                                                                    uu____4297
                                                                     in
                                                                    uu____4259
                                                                    ::
                                                                    uu____4272
                                                                     in
                                                                    uu____4234
                                                                    ::
                                                                    uu____4247
                                                                     in
                                                                    uu____4209
                                                                    ::
                                                                    uu____4222
                                                                     in
                                                                    uu____4184
                                                                    ::
                                                                    uu____4197
                                                                     in
                                                                    uu____4159
                                                                    ::
                                                                    uu____4172
                                                                     in
                                                                    uu____4134
                                                                    ::
                                                                    uu____4147
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4122
                                                                     in
                                                                    uu____4097
                                                                    ::
                                                                    uu____4110
                                                                     in
                                                                    uu____4072
                                                                    ::
                                                                    uu____4085
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4060
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4048
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4036
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4024
                                                                     in
                                                                    uu____3999
                                                                    ::
                                                                    uu____4012
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3987
                                                                     in
                                                                    uu____3962
                                                                    ::
                                                                    uu____3975
                                                                     in
                                                                    uu____3937
                                                                    ::
                                                                    uu____3950
                                                                     in
                                                                    uu____3912
                                                                    ::
                                                                    uu____3925
                                                                     in
                                                                    uu____3887
                                                                    ::
                                                                    uu____3900
                                                                     in
                                                                    uu____3862
                                                                    ::
                                                                    uu____3875
                                                                     in
                                                                    uu____3837
                                                                    ::
                                                                    uu____3850
                                                                     in
                                                                    uu____3812
                                                                    ::
                                                                    uu____3825
                                                                     in
                                                                    uu____3787
                                                                    ::
                                                                    uu____3800
                                                                     in
                                                                    uu____3762
                                                                    ::
                                                                    uu____3775
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3750
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3738
                                                                     in
                                                                    uu____3713
                                                                    ::
                                                                    uu____3726
                                                                     in
                                                                    uu____3688
                                                                    ::
                                                                    uu____3701
                                                                     in
                                                                    uu____3663
                                                                    ::
                                                                    uu____3676
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3651
                                                                     in
                                                                    uu____3626
                                                                    ::
                                                                    uu____3639
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3614
                                                                     in
                                                                    uu____3589
                                                                    ::
                                                                    uu____3602
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3577
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3565
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3553
                                                                     in
                                                                    uu____3528
                                                                    ::
                                                                    uu____3541
                                                                     in
                                                                    uu____3503
                                                                    ::
                                                                    uu____3516
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3491
                                                                     in
                                                                  uu____3466
                                                                    ::
                                                                    uu____3479
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_ifuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                  ::
                                                                  uu____3454
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_fuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of recursive functions to try initially (default 2)")
                                                                :: uu____3442
                                                               in
                                                            uu____3417 ::
                                                              uu____3430
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "include",
                                                            (ReverseAccumulated
                                                               (PathStr
                                                                  "path")),
                                                            "A directory in which to search for files included on the command line")
                                                            :: uu____3405
                                                           in
                                                        uu____3380 ::
                                                          uu____3393
                                                         in
                                                      uu____3355 ::
                                                        uu____3368
                                                       in
                                                    uu____3330 :: uu____3343
                                                     in
                                                  (FStar_Getopt.noshort,
                                                    "hint_file",
                                                    (PathStr "path"),
                                                    "Read/write hints to <path> (instead of module-specific hints files)")
                                                    :: uu____3318
                                                   in
                                                uu____3293 :: uu____3306  in
                                              uu____3268 :: uu____3281  in
                                            (FStar_Getopt.noshort,
                                              "extract_namespace",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "namespace name")))),
                                              "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                              :: uu____3256
                                             in
                                          (FStar_Getopt.noshort,
                                            "extract_module",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr "module_name")))),
                                            "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                            :: uu____3244
                                           in
                                        (FStar_Getopt.noshort, "extract",
                                          (Accumulated
                                             (SimpleStr
                                                "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                          "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                          :: uu____3232
                                         in
                                      uu____3207 :: uu____3220  in
                                    uu____3182 :: uu____3195  in
                                  (FStar_Getopt.noshort, "dump_module",
                                    (Accumulated (SimpleStr "module_name")),
                                    "") :: uu____3170
                                   in
                                uu____3145 :: uu____3158  in
                              uu____3120 :: uu____3133  in
                            uu____3095 :: uu____3108  in
                          (FStar_Getopt.noshort, "dep",
                            (EnumStr ["make"; "graph"; "full"]),
                            "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                            :: uu____3083
                           in
                        (FStar_Getopt.noshort, "defensive",
                          (EnumStr ["no"; "warn"; "fail"]),
                          "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                          :: uu____3071
                         in
                      (FStar_Getopt.noshort, "debug_level",
                        (Accumulated
                           (OpenEnumStr
                              (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                        "Control the verbosity of debugging info") ::
                        uu____3059
                       in
                    (FStar_Getopt.noshort, "debug",
                      (Accumulated (SimpleStr "module_name")),
                      "Print lots of debugging information while checking module")
                      :: uu____3047
                     in
                  (FStar_Getopt.noshort, "codegen-lib",
                    (Accumulated (SimpleStr "namespace")),
                    "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                    :: uu____3035
                   in
                (FStar_Getopt.noshort, "codegen",
                  (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                  "Generate code for further compilation to executable code, or build a compiler plugin")
                  :: uu____3023
                 in
              uu____2998 :: uu____3011  in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____2986
             in
          uu____2961 :: uu____2974  in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____2949
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____2937
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___82_5603  ->
             match uu___82_5603 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____2925

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5626  ->
    let uu____5629 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5656  ->
         match uu____5656 with
         | (short,long,typ,doc) ->
             let uu____5672 =
               let uu____5684 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5684, doc)  in
             mk_spec uu____5672) uu____5629

let (settable : Prims.string -> Prims.bool) =
  fun uu___83_5694  ->
    match uu___83_5694 with
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
    | uu____5695 -> false
  
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
       (fun uu____5769  ->
          match uu____5769 with
          | (uu____5781,x,uu____5783,uu____5784) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5846  ->
          match uu____5846 with
          | (uu____5858,x,uu____5860,uu____5861) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5872  ->
    let uu____5873 = specs ()  in display_usage_aux uu____5873
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5897 -> true
    | uu____5898 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5905 -> uu____5905
  
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
          let uu____5933 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5933
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5961  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5966 =
             let uu____5969 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5969 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5966)
       in
    let uu____6018 =
      let uu____6021 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6021
       in
    (res, uu____6018)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6055  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6090 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6090 (fun x  -> ())  in
     (let uu____6096 =
        let uu____6101 =
          let uu____6102 = FStar_List.map mk_string old_verify_module  in
          List uu____6102  in
        ("verify_module", uu____6101)  in
      set_option' uu____6096);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6112 =
        let uu____6113 =
          let uu____6114 =
            let uu____6115 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6115  in
          (FStar_String.length f1) - uu____6114  in
        uu____6113 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6112  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6121 = get_lax ()  in
    if uu____6121
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6131 = module_name_of_file_name fn  in should_verify uu____6131
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6137 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6137
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6145 = should_verify m  in
    if uu____6145 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6153  ->
    let uu____6154 = get_no_default_includes ()  in
    if uu____6154
    then get_include ()
    else
      (let lib_paths =
         let uu____6161 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6161 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6170 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6170
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6184 =
         let uu____6187 = get_include ()  in
         FStar_List.append uu____6187 ["."]  in
       FStar_List.append lib_paths uu____6184)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____6200 = FStar_Util.smap_try_find file_map filename  in
    match uu____6200 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            let uu____6216 = FStar_Util.is_path_absolute filename  in
            if uu____6216
            then
              (if FStar_Util.file_exists filename
               then FStar_Pervasives_Native.Some filename
               else FStar_Pervasives_Native.None)
            else
              (let uu____6223 =
                 let uu____6226 = include_path ()  in
                 FStar_List.rev uu____6226  in
               FStar_Util.find_map uu____6223
                 (fun p  ->
                    let path =
                      if p = "."
                      then filename
                      else FStar_Util.join_paths p filename  in
                    if FStar_Util.file_exists path
                    then FStar_Pervasives_Native.Some path
                    else FStar_Pervasives_Native.None))
          with | uu____6242 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____6251  ->
    let uu____6252 = get_prims ()  in
    match uu____6252 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6256 = find_file filename  in
        (match uu____6256 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6260 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6260)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6266  ->
    let uu____6267 = prims ()  in FStar_Util.basename uu____6267
  
let (pervasives : unit -> Prims.string) =
  fun uu____6272  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____6274 = find_file filename  in
    match uu____6274 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____6278 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6278
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6283  ->
    let uu____6284 = pervasives ()  in FStar_Util.basename uu____6284
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6289  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____6291 = find_file filename  in
    match uu____6291 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____6295 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6295
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____6301 = get_odir ()  in
    match uu____6301 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____6310 = get_cache_dir ()  in
    match uu____6310 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6314 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____6314
  
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
             let uu____6380 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____6380  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____6388 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6388 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6458 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6458 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6467  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6472  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6479  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6484  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____6489  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6495 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6501 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6507 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6513 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6520  ->
    let uu____6521 = get_codegen ()  in
    FStar_Util.map_opt uu____6521
      (fun uu___84_6525  ->
         match uu___84_6525 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6526 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6535  ->
    let uu____6536 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6536
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6553  -> let uu____6554 = get_debug ()  in uu____6554 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6564 = get_debug ()  in
    FStar_All.pipe_right uu____6564 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6581 = get_debug ()  in
       FStar_All.pipe_right uu____6581 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6590  -> let uu____6591 = get_defensive ()  in uu____6591 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6596  ->
    let uu____6597 = get_defensive ()  in uu____6597 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6604  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6609  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6614  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6619  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6625 = get_dump_module ()  in
    FStar_All.pipe_right uu____6625 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6634  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6639  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6645 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6645
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6675  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6680  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6685  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6692  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6697  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6702  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6707  ->
    let uu____6708 = get_initial_fuel ()  in
    let uu____6709 = get_max_fuel ()  in Prims.min uu____6708 uu____6709
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6714  ->
    let uu____6715 = get_initial_ifuel ()  in
    let uu____6716 = get_max_ifuel ()  in Prims.min uu____6715 uu____6716
  
let (interactive : unit -> Prims.bool) =
  fun uu____6721  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6726  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6733  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6738  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6743  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6748  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6753  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6758  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6763  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6768  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6773  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6778  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6783  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6790 = get_no_extract ()  in
    FStar_All.pipe_right uu____6790
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6801  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6806  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6811  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6818  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6823  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6828  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6833  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6838  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6843  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6848  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6853  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____6858  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____6863  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6870  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____6875  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6880  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6885  ->
    let uu____6886 = get_smtencoding_nl_arith_repr ()  in
    uu____6886 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6891  ->
    let uu____6892 = get_smtencoding_nl_arith_repr ()  in
    uu____6892 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6897  ->
    let uu____6898 = get_smtencoding_nl_arith_repr ()  in
    uu____6898 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6903  ->
    let uu____6904 = get_smtencoding_l_arith_repr ()  in
    uu____6904 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6909  ->
    let uu____6910 = get_smtencoding_l_arith_repr ()  in
    uu____6910 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6915  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6920  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6925  -> get_tactic_trace_d () 
let (timing : unit -> Prims.bool) = fun uu____6930  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____6935  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____6940  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____6945  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____6950  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____6955  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____6960  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6967  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____6972  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____6985  ->
    let uu____6986 = get_using_facts_from ()  in
    match uu____6986 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7024  ->
    let uu____7025 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____7025
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7032  ->
    let uu____7033 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____7033 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7036 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7043  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____7048  ->
    let uu____7049 = get_smt ()  in
    match uu____7049 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7059  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____7064  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____7069  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7074  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____7079  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7084  ->
    (get_use_two_phase_tc ()) &&
      (let uu____7086 = lax ()  in Prims.op_Negation uu____7086)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7091  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7096  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7101  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7106  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7113 = get_extract ()  in
    match uu____7113 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7124 =
            let uu____7137 = get_no_extract ()  in
            let uu____7140 = get_extract_namespace ()  in
            let uu____7143 = get_extract_module ()  in
            (uu____7137, uu____7140, uu____7143)  in
          match uu____7124 with
          | ([],[],[]) -> ()
          | uu____7158 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7206,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7225 -> false  in
          let uu____7234 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7268  ->
                    match uu____7268 with
                    | (path,uu____7276) -> matches_path m_components path))
             in
          match uu____7234 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____7287,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____7307 = get_extract_namespace ()  in
          match uu____7307 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____7323 = get_extract_module ()  in
          match uu____7323 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____7335 = no_extract m1  in Prims.op_Negation uu____7335) &&
          (let uu____7337 =
             let uu____7346 = get_extract_namespace ()  in
             let uu____7349 = get_extract_module ()  in
             (uu____7346, uu____7349)  in
           (match uu____7337 with
            | ([],[]) -> true
            | uu____7360 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  