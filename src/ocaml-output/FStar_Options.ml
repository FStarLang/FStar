open Prims
type debug_level_t =
  | Low 
  | Medium 
  | High 
  | Extreme 
  | Other of Prims.string [@@deriving show]
let (uu___is_Low : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | Low  -> true | uu____10 -> false 
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____16 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | High  -> true | uu____22 -> false 
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____28 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____35 -> false
  
let (__proj__Other__item___0 : debug_level_t -> Prims.string) =
  fun projectee  -> match projectee with | Other _0 -> _0 
type option_val =
  | Bool of Prims.bool 
  | String of Prims.string 
  | Path of Prims.string 
  | Int of Prims.int 
  | List of option_val Prims.list 
  | Unset [@@deriving show]
let (uu___is_Bool : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____71 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____85 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____99 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____113 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____129 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____148 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _0_4  -> Bool _0_4 
let (mk_string : Prims.string -> option_val) = fun _0_5  -> String _0_5 
let (mk_path : Prims.string -> option_val) = fun _0_6  -> Path _0_6 
let (mk_int : Prims.int -> option_val) = fun _0_7  -> Int _0_7 
let (mk_list : option_val Prims.list -> option_val) = fun _0_8  -> List _0_8 
type options =
  | Set 
  | Reset 
  | Restore [@@deriving show]
let (uu___is_Set : options -> Prims.bool) =
  fun projectee  -> match projectee with | Set  -> true | uu____176 -> false 
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____182 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____188 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____206  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____234  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____262  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___38_290  ->
    match uu___38_290 with
    | Bool b -> b
    | uu____292 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___39_297  ->
    match uu___39_297 with
    | Int b -> b
    | uu____299 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___40_304  ->
    match uu___40_304 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____307 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___41_314  ->
    match uu___41_314 with
    | List ts -> ts
    | uu____320 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____329 .
    (option_val -> 'Auu____329) -> option_val -> 'Auu____329 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____347 = as_list' x  in
      FStar_All.pipe_right uu____347 (FStar_List.map as_t)
  
let as_option :
  'Auu____360 .
    (option_val -> 'Auu____360) ->
      option_val -> 'Auu____360 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___42_375  ->
      match uu___42_375 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____379 = as_t v1  in FStar_Pervasives_Native.Some uu____379
  
type optionstate = option_val FStar_Util.smap[@@deriving show]
let (fstar_options : optionstate Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : unit -> optionstate) =
  fun uu____403  ->
    let uu____404 = FStar_ST.op_Bang fstar_options  in
    FStar_List.hd uu____404
  
let (pop : unit -> unit) =
  fun uu____438  ->
    let uu____439 = FStar_ST.op_Bang fstar_options  in
    match uu____439 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____469::[] -> failwith "TOO MANY POPS!"
    | uu____470::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____505  ->
    let uu____506 =
      let uu____509 =
        let uu____512 = peek ()  in FStar_Util.smap_copy uu____512  in
      let uu____515 = FStar_ST.op_Bang fstar_options  in uu____509 ::
        uu____515
       in
    FStar_ST.op_Colon_Equals fstar_options uu____506
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____581 = FStar_ST.op_Bang fstar_options  in
    match uu____581 with
    | [] -> failwith "set on empty option stack"
    | uu____611::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
  
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  -> let uu____652 = peek ()  in FStar_Util.smap_add uu____652 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____663  -> match uu____663 with | (k,v1) -> set_option k v1 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____685 = push ()  in
    let retv = f ()  in let uu____687 = pop ()  in retv
  
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____710 =
      let uu____713 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____713
       in
    FStar_ST.op_Colon_Equals light_off_files uu____710
  
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
  fun uu____1160  ->
    let o = peek ()  in
    let uu____1162 = FStar_Util.smap_clear o  in
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1177  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    let uu____1181 = FStar_ST.op_Colon_Equals fstar_options [o]  in
    let uu____1213 = FStar_ST.op_Colon_Equals light_off_files []  in init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1246 =
      let uu____1249 = peek ()  in FStar_Util.smap_try_find uu____1249 s  in
    match uu____1246 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1259 . Prims.string -> (option_val -> 'Auu____1259) -> 'Auu____1259
  = fun s  -> fun c  -> c (get_option s) 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1279  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1286  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1293  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1300  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1309  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1318  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1327  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1336  -> lookup_opt "debug_level" (as_list as_string) 
let (get_defensive : unit -> Prims.string) =
  fun uu____1343  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1350  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1357  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1362  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1367  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1374  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_inference : unit -> Prims.bool) =
  fun uu____1381  -> lookup_opt "eager_inference" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1386  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1395  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1408  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1417  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1424  -> lookup_opt "fs_typ_app" as_bool 
let (get_fstar_home : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1431  -> lookup_opt "fstar_home" (as_option as_string) 
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
  fun uu___43_1846  ->
    match uu___43_1846 with
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
      let uu____2023 = FStar_ST.op_Bang _platform  in
      let uu____2047 = FStar_ST.op_Bang _compiler  in
      let uu____2071 = FStar_ST.op_Bang _date  in
      let uu____2095 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1999
        uu____2023 uu____2047 uu____2071 uu____2095
       in
    FStar_Util.print_string uu____1998
  
let display_usage_aux :
  'Auu____2125 'Auu____2126 .
    ('Auu____2125,Prims.string,'Auu____2126 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    let uu____2156 = FStar_Util.print_string "fstar.exe [options] file[s]\n"
       in
    FStar_List.iter
      (fun uu____2174  ->
         match uu____2174 with
         | (uu____2185,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2197 =
                      let uu____2198 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2198  in
                    FStar_Util.print_string uu____2197
                  else
                    (let uu____2200 =
                       let uu____2201 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2201 doc  in
                     FStar_Util.print_string uu____2200)
              | FStar_Getopt.OneArg (uu____2202,argname) ->
                  if doc = ""
                  then
                    let uu____2210 =
                      let uu____2211 = FStar_Util.colorize_bold flag  in
                      let uu____2212 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2211 uu____2212
                       in
                    FStar_Util.print_string uu____2210
                  else
                    (let uu____2214 =
                       let uu____2215 = FStar_Util.colorize_bold flag  in
                       let uu____2216 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2215
                         uu____2216 doc
                        in
                     FStar_Util.print_string uu____2214))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2242 = o  in
    match uu____2242 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2275 =
                let uu____2276 = f ()  in set_option name uu____2276  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2291 = f x  in set_option name uu____2291
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2310 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2310  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2333 =
        let uu____2336 = lookup_opt name as_list'  in
        FStar_List.append uu____2336 [value]  in
      mk_list uu____2333
  
let accumulate_string :
  'Auu____2349 .
    Prims.string -> ('Auu____2349 -> Prims.string) -> 'Auu____2349 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2370 =
          let uu____2371 =
            let uu____2372 = post_processor value  in mk_string uu____2372
             in
          accumulated_option name uu____2371  in
        set_option name uu____2370
  
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
[@@deriving show]
let (uu___is_Const : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____2456 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2470 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2483 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2490 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2504 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2520 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2546 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2585 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2620 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2634 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2655 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2692 -> true
    | uu____2693 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2700 -> uu____2700
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2720 ->
              let uu____2721 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2721 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2725 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2725
          | PathStr uu____2728 -> mk_path str_val
          | SimpleStr uu____2729 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2734 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2749 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2749
          | Accumulated elem_spec ->
              let v1 = parse_opt_val opt_name elem_spec str_val  in
              accumulated_option opt_name v1
          | ReverseAccumulated elem_spec ->
              let v1 = parse_opt_val opt_name elem_spec str_val  in
              reverse_accumulated_option opt_name v1
          | WithSideEffect (side_effect,elem_spec) ->
              let uu____2762 = side_effect ()  in
              parse_opt_val opt_name elem_spec str_val
        with
        | InvalidArgument opt_name1 ->
            let uu____2768 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2768
  
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
    | PostProcessed (uu____2805,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2815,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2842 = desc_of_opt_type typ  in
      match uu____2842 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2848  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  ->
    let pp = as_string p  in let uu____2859 = FStar_Util.mkdir false pp  in p
  
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2865 =
      let uu____2866 = as_string s  in FStar_String.lowercase uu____2866  in
    mk_string uu____2865
  
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2887  ->
    let uu____2898 =
      let uu____2909 =
        let uu____2920 =
          let uu____2929 = let uu____2930 = mk_bool true  in Const uu____2930
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2929,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
           in
        let uu____2931 =
          let uu____2942 =
            let uu____2953 =
              let uu____2964 =
                let uu____2975 =
                  let uu____2986 =
                    let uu____2997 =
                      let uu____3008 =
                        let uu____3019 =
                          let uu____3028 =
                            let uu____3029 = mk_bool true  in
                            Const uu____3029  in
                          (FStar_Getopt.noshort, "detail_errors", uu____3028,
                            "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                           in
                        let uu____3030 =
                          let uu____3041 =
                            let uu____3050 =
                              let uu____3051 = mk_bool true  in
                              Const uu____3051  in
                            (FStar_Getopt.noshort, "detail_hint_replay",
                              uu____3050,
                              "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                             in
                          let uu____3052 =
                            let uu____3063 =
                              let uu____3072 =
                                let uu____3073 = mk_bool true  in
                                Const uu____3073  in
                              (FStar_Getopt.noshort, "doc", uu____3072,
                                "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                               in
                            let uu____3074 =
                              let uu____3085 =
                                let uu____3096 =
                                  let uu____3105 =
                                    let uu____3106 = mk_bool true  in
                                    Const uu____3106  in
                                  (FStar_Getopt.noshort, "eager_inference",
                                    uu____3105,
                                    "Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                   in
                                let uu____3107 =
                                  let uu____3118 =
                                    let uu____3129 =
                                      let uu____3140 =
                                        let uu____3151 =
                                          let uu____3160 =
                                            let uu____3161 = mk_bool true  in
                                            Const uu____3161  in
                                          (FStar_Getopt.noshort,
                                            "expose_interfaces", uu____3160,
                                            "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                           in
                                        let uu____3162 =
                                          let uu____3173 =
                                            let uu____3184 =
                                              let uu____3193 =
                                                let uu____3194 = mk_bool true
                                                   in
                                                Const uu____3194  in
                                              (FStar_Getopt.noshort,
                                                "hide_uvar_nums", uu____3193,
                                                "Don't print unification variable numbers")
                                               in
                                            let uu____3195 =
                                              let uu____3206 =
                                                let uu____3217 =
                                                  let uu____3226 =
                                                    let uu____3227 =
                                                      mk_bool true  in
                                                    Const uu____3227  in
                                                  (FStar_Getopt.noshort,
                                                    "hint_info", uu____3226,
                                                    "Print information regarding hints (deprecated; use --query_stats instead)")
                                                   in
                                                let uu____3228 =
                                                  let uu____3239 =
                                                    let uu____3248 =
                                                      let uu____3249 =
                                                        mk_bool true  in
                                                      Const uu____3249  in
                                                    (FStar_Getopt.noshort,
                                                      "in", uu____3248,
                                                      "Legacy interactive mode; reads input from stdin")
                                                     in
                                                  let uu____3250 =
                                                    let uu____3261 =
                                                      let uu____3270 =
                                                        let uu____3271 =
                                                          mk_bool true  in
                                                        Const uu____3271  in
                                                      (FStar_Getopt.noshort,
                                                        "ide", uu____3270,
                                                        "JSON-based interactive mode for IDEs")
                                                       in
                                                    let uu____3272 =
                                                      let uu____3283 =
                                                        let uu____3294 =
                                                          let uu____3303 =
                                                            let uu____3304 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3304
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "indent",
                                                            uu____3303,
                                                            "Parses and outputs the files on the command line")
                                                           in
                                                        let uu____3305 =
                                                          let uu____3316 =
                                                            let uu____3327 =
                                                              let uu____3338
                                                                =
                                                                let uu____3347
                                                                  =
                                                                  let uu____3348
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                  Const
                                                                    uu____3348
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "lax",
                                                                  uu____3347,
                                                                  "Run the lax-type checker only (admit all verification conditions)")
                                                                 in
                                                              let uu____3349
                                                                =
                                                                let uu____3360
                                                                  =
                                                                  let uu____3371
                                                                    =
                                                                    let uu____3380
                                                                    =
                                                                    let uu____3381
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3381
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3380,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                  let uu____3382
                                                                    =
                                                                    let uu____3393
                                                                    =
                                                                    let uu____3402
                                                                    =
                                                                    let uu____3403
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3403
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3402,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3404
                                                                    =
                                                                    let uu____3415
                                                                    =
                                                                    let uu____3426
                                                                    =
                                                                    let uu____3437
                                                                    =
                                                                    let uu____3448
                                                                    =
                                                                    let uu____3457
                                                                    =
                                                                    let uu____3458
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3458
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3457,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3459
                                                                    =
                                                                    let uu____3470
                                                                    =
                                                                    let uu____3481
                                                                    =
                                                                    let uu____3490
                                                                    =
                                                                    let uu____3491
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3491
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3490,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3492
                                                                    =
                                                                    let uu____3503
                                                                    =
                                                                    let uu____3514
                                                                    =
                                                                    let uu____3523
                                                                    =
                                                                    let uu____3524
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3524
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3523,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3525
                                                                    =
                                                                    let uu____3536
                                                                    =
                                                                    let uu____3545
                                                                    =
                                                                    let uu____3546
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3546
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3545,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3547
                                                                    =
                                                                    let uu____3558
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
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3567,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3569
                                                                    =
                                                                    let uu____3580
                                                                    =
                                                                    let uu____3591
                                                                    =
                                                                    let uu____3602
                                                                    =
                                                                    let uu____3611
                                                                    =
                                                                    let uu____3612
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3612
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3611,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3613
                                                                    =
                                                                    let uu____3624
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
                                                                    "print_effect_args",
                                                                    uu____3633,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3635
                                                                    =
                                                                    let uu____3646
                                                                    =
                                                                    let uu____3655
                                                                    =
                                                                    let uu____3656
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3656
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3655,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3657
                                                                    =
                                                                    let uu____3668
                                                                    =
                                                                    let uu____3677
                                                                    =
                                                                    let uu____3678
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3678
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3677,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3679
                                                                    =
                                                                    let uu____3690
                                                                    =
                                                                    let uu____3699
                                                                    =
                                                                    let uu____3700
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3700
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3699,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3701
                                                                    =
                                                                    let uu____3712
                                                                    =
                                                                    let uu____3721
                                                                    =
                                                                    let uu____3722
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3722
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3721,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3723
                                                                    =
                                                                    let uu____3734
                                                                    =
                                                                    let uu____3743
                                                                    =
                                                                    let uu____3744
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3744
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3743,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3745
                                                                    =
                                                                    let uu____3756
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
                                                                    "query_stats",
                                                                    uu____3765,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3767
                                                                    =
                                                                    let uu____3778
                                                                    =
                                                                    let uu____3787
                                                                    =
                                                                    let uu____3788
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3788
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3787,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3789
                                                                    =
                                                                    let uu____3800
                                                                    =
                                                                    let uu____3811
                                                                    =
                                                                    let uu____3820
                                                                    =
                                                                    let uu____3821
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3821
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3820,
                                                                    " ")  in
                                                                    let uu____3822
                                                                    =
                                                                    let uu____3833
                                                                    =
                                                                    let uu____3844
                                                                    =
                                                                    let uu____3855
                                                                    =
                                                                    let uu____3866
                                                                    =
                                                                    let uu____3877
                                                                    =
                                                                    let uu____3886
                                                                    =
                                                                    let uu____3887
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3887
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____3886,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____3888
                                                                    =
                                                                    let uu____3899
                                                                    =
                                                                    let uu____3908
                                                                    =
                                                                    let uu____3909
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3909
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3908,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____3910
                                                                    =
                                                                    let uu____3921
                                                                    =
                                                                    let uu____3932
                                                                    =
                                                                    let uu____3941
                                                                    =
                                                                    let uu____3942
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3942
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3941,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____3943
                                                                    =
                                                                    let uu____3954
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
                                                                    "trace_error",
                                                                    uu____3963,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____3965
                                                                    =
                                                                    let uu____3976
                                                                    =
                                                                    let uu____3985
                                                                    =
                                                                    let uu____3986
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3986
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3985,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____3987
                                                                    =
                                                                    let uu____3998
                                                                    =
                                                                    let uu____4007
                                                                    =
                                                                    let uu____4008
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4008
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4007,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4009
                                                                    =
                                                                    let uu____4020
                                                                    =
                                                                    let uu____4029
                                                                    =
                                                                    let uu____4030
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4030
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4029,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4031
                                                                    =
                                                                    let uu____4042
                                                                    =
                                                                    let uu____4051
                                                                    =
                                                                    let uu____4052
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4052
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4051,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4053
                                                                    =
                                                                    let uu____4064
                                                                    =
                                                                    let uu____4073
                                                                    =
                                                                    let uu____4074
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4074
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4073,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4075
                                                                    =
                                                                    let uu____4086
                                                                    =
                                                                    let uu____4095
                                                                    =
                                                                    let uu____4096
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4096
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4095,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4097
                                                                    =
                                                                    let uu____4108
                                                                    =
                                                                    let uu____4119
                                                                    =
                                                                    let uu____4128
                                                                    =
                                                                    let uu____4129
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4129
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4128,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4130
                                                                    =
                                                                    let uu____4141
                                                                    =
                                                                    let uu____4152
                                                                    =
                                                                    let uu____4163
                                                                    =
                                                                    let uu____4174
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
                                                                    "__temp_fast_implicits",
                                                                    uu____4183,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4185
                                                                    =
                                                                    let uu____4196
                                                                    =
                                                                    let uu____4206
                                                                    =
                                                                    let uu____4207
                                                                    =
                                                                    let uu____4215
                                                                    =
                                                                    let uu____4216
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4216
                                                                     in
                                                                    ((fun
                                                                    uu____4222
                                                                     ->
                                                                    let uu____4223
                                                                    =
                                                                    display_version
                                                                    ()  in
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4215)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4207
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4206,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4226
                                                                    =
                                                                    let uu____4238
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
                                                                    "warn_default_effects",
                                                                    uu____4247,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4249
                                                                    =
                                                                    let uu____4260
                                                                    =
                                                                    let uu____4271
                                                                    =
                                                                    let uu____4280
                                                                    =
                                                                    let uu____4281
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4281
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4280,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4282
                                                                    =
                                                                    let uu____4293
                                                                    =
                                                                    let uu____4304
                                                                    =
                                                                    let uu____4315
                                                                    =
                                                                    let uu____4326
                                                                    =
                                                                    let uu____4337
                                                                    =
                                                                    let uu____4346
                                                                    =
                                                                    let uu____4347
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4347
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4346,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4348
                                                                    =
                                                                    let uu____4359
                                                                    =
                                                                    let uu____4368
                                                                    =
                                                                    let uu____4369
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4369
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4368,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4370
                                                                    =
                                                                    let uu____4381
                                                                    =
                                                                    let uu____4392
                                                                    =
                                                                    let uu____4401
                                                                    =
                                                                    let uu____4402
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4402
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    uu____4401,
                                                                    "Extract interfaces from the dependencies and use them for verification")
                                                                     in
                                                                    let uu____4403
                                                                    =
                                                                    let uu____4414
                                                                    =
                                                                    let uu____4424
                                                                    =
                                                                    let uu____4425
                                                                    =
                                                                    let uu____4433
                                                                    =
                                                                    let uu____4434
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4434
                                                                     in
                                                                    ((fun
                                                                    uu____4440
                                                                     ->
                                                                    let uu____4441
                                                                    =
                                                                    let uu____4442
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4442
                                                                     in
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4433)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4425
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4424,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4414]
                                                                     in
                                                                    uu____4392
                                                                    ::
                                                                    uu____4403
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4381
                                                                     in
                                                                    uu____4359
                                                                    ::
                                                                    uu____4370
                                                                     in
                                                                    uu____4337
                                                                    ::
                                                                    uu____4348
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'false')")
                                                                    ::
                                                                    uu____4326
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4315
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4304
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4293
                                                                     in
                                                                    uu____4271
                                                                    ::
                                                                    uu____4282
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4260
                                                                     in
                                                                    uu____4238
                                                                    ::
                                                                    uu____4249
                                                                     in
                                                                    uu____4196
                                                                    ::
                                                                    uu____4226
                                                                     in
                                                                    uu____4174
                                                                    ::
                                                                    uu____4185
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4163
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4152
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4141
                                                                     in
                                                                    uu____4119
                                                                    ::
                                                                    uu____4130
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4108
                                                                     in
                                                                    uu____4086
                                                                    ::
                                                                    uu____4097
                                                                     in
                                                                    uu____4064
                                                                    ::
                                                                    uu____4075
                                                                     in
                                                                    uu____4042
                                                                    ::
                                                                    uu____4053
                                                                     in
                                                                    uu____4020
                                                                    ::
                                                                    uu____4031
                                                                     in
                                                                    uu____3998
                                                                    ::
                                                                    uu____4009
                                                                     in
                                                                    uu____3976
                                                                    ::
                                                                    uu____3987
                                                                     in
                                                                    uu____3954
                                                                    ::
                                                                    uu____3965
                                                                     in
                                                                    uu____3932
                                                                    ::
                                                                    uu____3943
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3921
                                                                     in
                                                                    uu____3899
                                                                    ::
                                                                    uu____3910
                                                                     in
                                                                    uu____3877
                                                                    ::
                                                                    uu____3888
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3866
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3855
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3844
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3833
                                                                     in
                                                                    uu____3811
                                                                    ::
                                                                    uu____3822
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3800
                                                                     in
                                                                    uu____3778
                                                                    ::
                                                                    uu____3789
                                                                     in
                                                                    uu____3756
                                                                    ::
                                                                    uu____3767
                                                                     in
                                                                    uu____3734
                                                                    ::
                                                                    uu____3745
                                                                     in
                                                                    uu____3712
                                                                    ::
                                                                    uu____3723
                                                                     in
                                                                    uu____3690
                                                                    ::
                                                                    uu____3701
                                                                     in
                                                                    uu____3668
                                                                    ::
                                                                    uu____3679
                                                                     in
                                                                    uu____3646
                                                                    ::
                                                                    uu____3657
                                                                     in
                                                                    uu____3624
                                                                    ::
                                                                    uu____3635
                                                                     in
                                                                    uu____3602
                                                                    ::
                                                                    uu____3613
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3591
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3580
                                                                     in
                                                                    uu____3558
                                                                    ::
                                                                    uu____3569
                                                                     in
                                                                    uu____3536
                                                                    ::
                                                                    uu____3547
                                                                     in
                                                                    uu____3514
                                                                    ::
                                                                    uu____3525
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3503
                                                                     in
                                                                    uu____3481
                                                                    ::
                                                                    uu____3492
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3470
                                                                     in
                                                                    uu____3448
                                                                    ::
                                                                    uu____3459
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3437
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3426
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3415
                                                                     in
                                                                    uu____3393
                                                                    ::
                                                                    uu____3404
                                                                     in
                                                                  uu____3371
                                                                    ::
                                                                    uu____3382
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "load",
                                                                  (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                  "Load compiled module")
                                                                  ::
                                                                  uu____3360
                                                                 in
                                                              uu____3338 ::
                                                                uu____3349
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "initial_ifuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                              :: uu____3327
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "initial_fuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of recursive functions to try initially (default 2)")
                                                            :: uu____3316
                                                           in
                                                        uu____3294 ::
                                                          uu____3305
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "include",
                                                        (ReverseAccumulated
                                                           (PathStr "path")),
                                                        "A directory in which to search for files included on the command line")
                                                        :: uu____3283
                                                       in
                                                    uu____3261 :: uu____3272
                                                     in
                                                  uu____3239 :: uu____3250
                                                   in
                                                uu____3217 :: uu____3228  in
                                              (FStar_Getopt.noshort,
                                                "hint_file",
                                                (PathStr "path"),
                                                "Read/write hints to <path> (instead of module-specific hints files)")
                                                :: uu____3206
                                               in
                                            uu____3184 :: uu____3195  in
                                          (FStar_Getopt.noshort,
                                            "fstar_home", (PathStr "dir"),
                                            "Set the FSTAR_HOME variable to <dir>")
                                            :: uu____3173
                                           in
                                        uu____3151 :: uu____3162  in
                                      (FStar_Getopt.noshort,
                                        "extract_namespace",
                                        (Accumulated
                                           (PostProcessed
                                              (pp_lowercase,
                                                (SimpleStr "namespace name")))),
                                        "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                        :: uu____3140
                                       in
                                    (FStar_Getopt.noshort, "extract_module",
                                      (Accumulated
                                         (PostProcessed
                                            (pp_lowercase,
                                              (SimpleStr "module_name")))),
                                      "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                      :: uu____3129
                                     in
                                  (FStar_Getopt.noshort, "extract",
                                    (Accumulated
                                       (SimpleStr
                                          "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                    "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                    :: uu____3118
                                   in
                                uu____3096 :: uu____3107  in
                              (FStar_Getopt.noshort, "dump_module",
                                (Accumulated (SimpleStr "module_name")), "")
                                :: uu____3085
                               in
                            uu____3063 :: uu____3074  in
                          uu____3041 :: uu____3052  in
                        uu____3019 :: uu____3030  in
                      (FStar_Getopt.noshort, "dep",
                        (EnumStr ["make"; "graph"; "full"]),
                        "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                        :: uu____3008
                       in
                    (FStar_Getopt.noshort, "defensive",
                      (EnumStr ["no"; "warn"; "fail"]),
                      "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                      :: uu____2997
                     in
                  (FStar_Getopt.noshort, "debug_level",
                    (Accumulated
                       (OpenEnumStr
                          (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                    "Control the verbosity of debugging info") :: uu____2986
                   in
                (FStar_Getopt.noshort, "debug",
                  (Accumulated (SimpleStr "module_name")),
                  "Print lots of debugging information while checking module")
                  :: uu____2975
                 in
              (FStar_Getopt.noshort, "codegen-lib",
                (Accumulated (SimpleStr "namespace")),
                "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                :: uu____2964
               in
            (FStar_Getopt.noshort, "codegen",
              (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
              "Generate code for further compilation to executable code, or build a compiler plugin")
              :: uu____2953
             in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2942
           in
        uu____2920 :: uu____2931  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2909
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2898

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5202  ->
    let uu____5205 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5230  ->
         match uu____5230 with
         | (short,long,typ,doc) ->
             let uu____5243 =
               let uu____5254 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5254, doc)  in
             mk_spec uu____5243) uu____5205

let (settable : Prims.string -> Prims.bool) =
  fun uu___44_5263  ->
    match uu___44_5263 with
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
    | uu____5264 -> false
  
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
       (fun uu____5323  ->
          match uu____5323 with
          | (uu____5334,x,uu____5336,uu____5337) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5383  ->
          match uu____5383 with
          | (uu____5394,x,uu____5396,uu____5397) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5406  ->
    let uu____5407 = specs ()  in display_usage_aux uu____5407
  
let (fstar_home : unit -> Prims.string) =
  fun uu____5424  ->
    let uu____5425 = get_fstar_home ()  in
    match uu____5425 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir ()  in
        let x1 = Prims.strcat x "/.."  in
        let uu____5430 =
          let uu____5431 =
            let uu____5436 = mk_string x1  in ("fstar_home", uu____5436)  in
          set_option' uu____5431  in
        x1
    | FStar_Pervasives_Native.Some x -> x
  
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5446 -> true
    | uu____5447 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5454 -> uu____5454
  
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
            (fun s1  ->
               let uu____5496 = FStar_Exn.raise (File_argument s1)  in ()) s
      with
      | File_argument s1 ->
          let uu____5502 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5502
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5530  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5535 =
             let uu____5538 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5538 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5535)
       in
    let uu____5595 =
      let uu____5598 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5598
       in
    (res, uu____5595)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____5636  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    let uu____5672 = if should_clear then clear () else init ()  in
    let r =
      let uu____5675 = specs ()  in
      FStar_Getopt.parse_cmdline uu____5675 (fun x  -> ())  in
    let uu____5680 =
      let uu____5681 =
        let uu____5686 =
          let uu____5687 = FStar_List.map mk_string old_verify_module  in
          List uu____5687  in
        ("verify_module", uu____5686)  in
      set_option' uu____5681  in
    r
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____5697 =
        let uu____5698 =
          let uu____5699 =
            let uu____5700 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____5700  in
          (FStar_String.length f1) - uu____5699  in
        uu____5698 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5697  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5706 = get_lax ()  in
    if uu____5706
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____5716 = module_name_of_file_name fn  in should_verify uu____5716
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5722 = get___temp_no_proj ()  in
    FStar_List.contains m uu____5722
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5730 = should_verify m  in
    if uu____5730 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____5738  ->
    let uu____5739 = get_no_default_includes ()  in
    if uu____5739
    then get_include ()
    else
      (let h = fstar_home ()  in
       let defs = universe_include_path_base_dirs  in
       let uu____5747 =
         let uu____5750 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x))
            in
         FStar_All.pipe_right uu____5750
           (FStar_List.filter FStar_Util.file_exists)
          in
       let uu____5763 =
         let uu____5766 = get_include ()  in
         FStar_List.append uu____5766 ["."]  in
       FStar_List.append uu____5747 uu____5763)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun filename  ->
    let uu____5776 = FStar_Util.is_path_absolute filename  in
    if uu____5776
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5783 =
         let uu____5786 = include_path ()  in FStar_List.rev uu____5786  in
       FStar_Util.find_map uu____5783
         (fun p  ->
            let path =
              if p = "." then filename else FStar_Util.join_paths p filename
               in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
  
let (prims : unit -> Prims.string) =
  fun uu____5801  ->
    let uu____5802 = get_prims ()  in
    match uu____5802 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____5806 = find_file filename  in
        (match uu____5806 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5810 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____5810)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____5816  ->
    let uu____5817 = prims ()  in FStar_Util.basename uu____5817
  
let (pervasives : unit -> Prims.string) =
  fun uu____5822  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____5824 = find_file filename  in
    match uu____5824 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5828 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5828
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____5833  ->
    let uu____5834 = pervasives ()  in FStar_Util.basename uu____5834
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____5839  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____5841 = find_file filename  in
    match uu____5841 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5845 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5845
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____5851 = get_odir ()  in
    match uu____5851 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____5860 = get_cache_dir ()  in
    match uu____5860 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____5864 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____5864
  
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
             let uu____5918 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             FStar_Ident.path_of_text uu____5918  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           let uu____5922 = FStar_Ident.path_of_text s1  in
           (uu____5922, true))
       in
    let uu____5923 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____5923 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____5993 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____5993 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6002  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6007  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6014  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6019  -> get_cache_checked_modules () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin [@@deriving show]
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6025 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6031 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6037 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6043 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6050  ->
    let uu____6051 = get_codegen ()  in
    FStar_Util.map_opt uu____6051
      (fun uu___45_6055  ->
         match uu___45_6055 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6056 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6065  ->
    let uu____6066 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6066
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6083  -> let uu____6084 = get_debug ()  in uu____6084 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6094 = get_debug ()  in
    FStar_All.pipe_right uu____6094 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6111 = get_debug ()  in
       FStar_All.pipe_right uu____6111 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6120  -> let uu____6121 = get_defensive ()  in uu____6121 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6126  ->
    let uu____6127 = get_defensive ()  in uu____6127 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6134  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6139  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6144  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6149  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6155 = get_dump_module ()  in
    FStar_All.pipe_right uu____6155 (FStar_List.contains s)
  
let (eager_inference : unit -> Prims.bool) =
  fun uu____6164  -> get_eager_inference () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6169  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6175 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6175
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6209  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6214  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6219  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6226  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6231  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6236  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6241  ->
    let uu____6242 = get_initial_fuel ()  in
    let uu____6243 = get_max_fuel ()  in Prims.min uu____6242 uu____6243
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6248  ->
    let uu____6249 = get_initial_ifuel ()  in
    let uu____6250 = get_max_ifuel ()  in Prims.min uu____6249 uu____6250
  
let (interactive : unit -> Prims.bool) =
  fun uu____6255  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6260  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6267  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6272  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6277  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6282  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6287  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6292  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6297  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6302  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6307  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6312  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6317  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6324 = get_no_extract ()  in
    FStar_All.pipe_right uu____6324
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6335  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6340  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6345  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6352  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6357  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6362  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6367  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6372  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6377  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6382  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6387  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____6392  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____6397  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6404  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____6409  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6414  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6419  ->
    let uu____6420 = get_smtencoding_nl_arith_repr ()  in
    uu____6420 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6425  ->
    let uu____6426 = get_smtencoding_nl_arith_repr ()  in
    uu____6426 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6431  ->
    let uu____6432 = get_smtencoding_nl_arith_repr ()  in
    uu____6432 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6437  ->
    let uu____6438 = get_smtencoding_l_arith_repr ()  in
    uu____6438 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6443  ->
    let uu____6444 = get_smtencoding_l_arith_repr ()  in
    uu____6444 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6449  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6454  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6459  -> get_tactic_trace_d () 
let (timing : unit -> Prims.bool) = fun uu____6464  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____6469  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____6474  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____6479  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____6484  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____6489  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____6494  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6501  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____6506  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____6517  ->
    let uu____6518 = get_using_facts_from ()  in
    match uu____6518 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____6554  ->
    let uu____6555 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____6555
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____6562  ->
    let uu____6563 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____6563 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____6566 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____6573  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____6578  ->
    let uu____6579 = get_smt ()  in
    match uu____6579 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____6589  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____6594  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____6599  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____6604  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____6609  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____6614  -> get_use_two_phase_tc () 
let (no_positivity : unit -> Prims.bool) =
  fun uu____6619  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____6624  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____6629  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____6634  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____6641 = get_extract ()  in
    match uu____6641 with
    | FStar_Pervasives_Native.Some extract_setting ->
        let uu____6651 =
          let uu____6652 =
            let uu____6665 = get_no_extract ()  in
            let uu____6668 = get_extract_namespace ()  in
            let uu____6671 = get_extract_module ()  in
            (uu____6665, uu____6668, uu____6671)  in
          match uu____6652 with
          | ([],[],[]) -> ()
          | uu____6686 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module"
           in
        let setting = parse_settings extract_setting  in
        let m_components = FStar_Ident.path_of_text m1  in
        let rec matches_path m_components1 path =
          match (m_components1, path) with
          | (uu____6732,[]) -> true
          | (m2::ms,p::ps) ->
              (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
          | uu____6751 -> false  in
        let uu____6760 =
          FStar_All.pipe_right setting
            (FStar_Util.try_find
               (fun uu____6794  ->
                  match uu____6794 with
                  | (path,uu____6802) -> matches_path m_components path))
           in
        (match uu____6760 with
         | FStar_Pervasives_Native.None  -> false
         | FStar_Pervasives_Native.Some (uu____6813,flag) -> flag)
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____6833 = get_extract_namespace ()  in
          match uu____6833 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____6849 = get_extract_module ()  in
          match uu____6849 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____6861 = no_extract m1  in Prims.op_Negation uu____6861) &&
          (let uu____6863 =
             let uu____6872 = get_extract_namespace ()  in
             let uu____6875 = get_extract_module ()  in
             (uu____6872, uu____6875)  in
           (match uu____6863 with
            | ([],[]) -> true
            | uu____6886 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  