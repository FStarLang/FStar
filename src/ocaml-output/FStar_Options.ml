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
  fun f  -> push (); (let retv = f ()  in pop (); retv) 
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
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1177  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
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
  = fun s  -> fun c  -> let uu____1275 = get_option s  in c uu____1275 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1280  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1287  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1294  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1301  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1310  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1319  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1328  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1337  -> lookup_opt "debug_level" (as_list as_string) 
let (get_defensive : unit -> Prims.string) =
  fun uu____1344  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1351  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1358  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1363  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1368  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1375  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_inference : unit -> Prims.bool) =
  fun uu____1382  -> lookup_opt "eager_inference" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1387  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1396  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1409  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1418  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1425  -> lookup_opt "fs_typ_app" as_bool 
let (get_fstar_home : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1432  -> lookup_opt "fstar_home" (as_option as_string) 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1439  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1444  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1451  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1458  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1463  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1470  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1477  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1482  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1487  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1492  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1499  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1506  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1511  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1516  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1521  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1526  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1531  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1536  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1541  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1548  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1555  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1560  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1565  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1572  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1579  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1586  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1593  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1598  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1603  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1608  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1613  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1618  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1623  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1628  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1633  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1640  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1647  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1654  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1661  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1666  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1671  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1676  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1681  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1686  -> lookup_opt "tactic_trace_d" as_int 
let (get_timing : unit -> Prims.bool) =
  fun uu____1691  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1696  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1701  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1706  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1711  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1716  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1721  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1728  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1735  ->
    let uu____1736 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1736
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1745  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1758  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1767  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1776  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1783  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1788  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1795  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1802  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1807  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1812  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1817  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1822  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1827  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1832  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1837  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1842  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___43_1847  ->
    match uu___43_1847 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1859 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1865 = get_debug_level ()  in
    FStar_All.pipe_right uu____1865
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____1998  ->
    let uu____1999 =
      let uu____2000 = FStar_ST.op_Bang _version  in
      let uu____2024 = FStar_ST.op_Bang _platform  in
      let uu____2048 = FStar_ST.op_Bang _compiler  in
      let uu____2072 = FStar_ST.op_Bang _date  in
      let uu____2096 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2000
        uu____2024 uu____2048 uu____2072 uu____2096
       in
    FStar_Util.print_string uu____1999
  
let display_usage_aux :
  'Auu____2126 'Auu____2127 .
    ('Auu____2126,Prims.string,'Auu____2127 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2175  ->
         match uu____2175 with
         | (uu____2186,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2198 =
                      let uu____2199 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2199  in
                    FStar_Util.print_string uu____2198
                  else
                    (let uu____2201 =
                       let uu____2202 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2202 doc  in
                     FStar_Util.print_string uu____2201)
              | FStar_Getopt.OneArg (uu____2203,argname) ->
                  if doc = ""
                  then
                    let uu____2211 =
                      let uu____2212 = FStar_Util.colorize_bold flag  in
                      let uu____2213 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2212 uu____2213
                       in
                    FStar_Util.print_string uu____2211
                  else
                    (let uu____2215 =
                       let uu____2216 = FStar_Util.colorize_bold flag  in
                       let uu____2217 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2216
                         uu____2217 doc
                        in
                     FStar_Util.print_string uu____2215))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2243 = o  in
    match uu____2243 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2276 =
                let uu____2277 = f ()  in set_option name uu____2277  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2292 = f x  in set_option name uu____2292
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2311 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2311  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2334 =
        let uu____2337 = lookup_opt name as_list'  in
        FStar_List.append uu____2337 [value]  in
      mk_list uu____2334
  
let accumulate_string :
  'Auu____2350 .
    Prims.string -> ('Auu____2350 -> Prims.string) -> 'Auu____2350 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2371 =
          let uu____2372 =
            let uu____2373 = post_processor value  in mk_string uu____2373
             in
          accumulated_option name uu____2372  in
        set_option name uu____2371
  
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
    match projectee with | Const _0 -> true | uu____2457 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2471 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2484 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2491 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2505 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2521 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2547 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2586 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2621 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2635 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2656 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2693 -> true
    | uu____2694 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2701 -> uu____2701
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2721 ->
              let uu____2722 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2722 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2726 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2726
          | PathStr uu____2729 -> mk_path str_val
          | SimpleStr uu____2730 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2735 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2750 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2750
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
            let uu____2769 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2769
  
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
    | PostProcessed (uu____2806,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2816,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2843 = desc_of_opt_type typ  in
      match uu____2843 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2849  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2866 =
      let uu____2867 = as_string s  in FStar_String.lowercase uu____2867  in
    mk_string uu____2866
  
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2888  ->
    let uu____2899 =
      let uu____2910 =
        let uu____2921 =
          let uu____2930 = let uu____2931 = mk_bool true  in Const uu____2931
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2930,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
           in
        let uu____2932 =
          let uu____2943 =
            let uu____2954 =
              let uu____2965 =
                let uu____2976 =
                  let uu____2987 =
                    let uu____2998 =
                      let uu____3009 =
                        let uu____3020 =
                          let uu____3029 =
                            let uu____3030 = mk_bool true  in
                            Const uu____3030  in
                          (FStar_Getopt.noshort, "detail_errors", uu____3029,
                            "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                           in
                        let uu____3031 =
                          let uu____3042 =
                            let uu____3051 =
                              let uu____3052 = mk_bool true  in
                              Const uu____3052  in
                            (FStar_Getopt.noshort, "detail_hint_replay",
                              uu____3051,
                              "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                             in
                          let uu____3053 =
                            let uu____3064 =
                              let uu____3073 =
                                let uu____3074 = mk_bool true  in
                                Const uu____3074  in
                              (FStar_Getopt.noshort, "doc", uu____3073,
                                "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                               in
                            let uu____3075 =
                              let uu____3086 =
                                let uu____3097 =
                                  let uu____3106 =
                                    let uu____3107 = mk_bool true  in
                                    Const uu____3107  in
                                  (FStar_Getopt.noshort, "eager_inference",
                                    uu____3106,
                                    "Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                   in
                                let uu____3108 =
                                  let uu____3119 =
                                    let uu____3130 =
                                      let uu____3141 =
                                        let uu____3152 =
                                          let uu____3161 =
                                            let uu____3162 = mk_bool true  in
                                            Const uu____3162  in
                                          (FStar_Getopt.noshort,
                                            "expose_interfaces", uu____3161,
                                            "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                           in
                                        let uu____3163 =
                                          let uu____3174 =
                                            let uu____3185 =
                                              let uu____3194 =
                                                let uu____3195 = mk_bool true
                                                   in
                                                Const uu____3195  in
                                              (FStar_Getopt.noshort,
                                                "hide_uvar_nums", uu____3194,
                                                "Don't print unification variable numbers")
                                               in
                                            let uu____3196 =
                                              let uu____3207 =
                                                let uu____3218 =
                                                  let uu____3227 =
                                                    let uu____3228 =
                                                      mk_bool true  in
                                                    Const uu____3228  in
                                                  (FStar_Getopt.noshort,
                                                    "hint_info", uu____3227,
                                                    "Print information regarding hints (deprecated; use --query_stats instead)")
                                                   in
                                                let uu____3229 =
                                                  let uu____3240 =
                                                    let uu____3249 =
                                                      let uu____3250 =
                                                        mk_bool true  in
                                                      Const uu____3250  in
                                                    (FStar_Getopt.noshort,
                                                      "in", uu____3249,
                                                      "Legacy interactive mode; reads input from stdin")
                                                     in
                                                  let uu____3251 =
                                                    let uu____3262 =
                                                      let uu____3271 =
                                                        let uu____3272 =
                                                          mk_bool true  in
                                                        Const uu____3272  in
                                                      (FStar_Getopt.noshort,
                                                        "ide", uu____3271,
                                                        "JSON-based interactive mode for IDEs")
                                                       in
                                                    let uu____3273 =
                                                      let uu____3284 =
                                                        let uu____3295 =
                                                          let uu____3304 =
                                                            let uu____3305 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3305
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "indent",
                                                            uu____3304,
                                                            "Parses and outputs the files on the command line")
                                                           in
                                                        let uu____3306 =
                                                          let uu____3317 =
                                                            let uu____3328 =
                                                              let uu____3339
                                                                =
                                                                let uu____3348
                                                                  =
                                                                  let uu____3349
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                  Const
                                                                    uu____3349
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "lax",
                                                                  uu____3348,
                                                                  "Run the lax-type checker only (admit all verification conditions)")
                                                                 in
                                                              let uu____3350
                                                                =
                                                                let uu____3361
                                                                  =
                                                                  let uu____3372
                                                                    =
                                                                    let uu____3381
                                                                    =
                                                                    let uu____3382
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3382
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3381,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                  let uu____3383
                                                                    =
                                                                    let uu____3394
                                                                    =
                                                                    let uu____3403
                                                                    =
                                                                    let uu____3404
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3404
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3403,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3405
                                                                    =
                                                                    let uu____3416
                                                                    =
                                                                    let uu____3427
                                                                    =
                                                                    let uu____3438
                                                                    =
                                                                    let uu____3449
                                                                    =
                                                                    let uu____3458
                                                                    =
                                                                    let uu____3459
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3459
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3458,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3460
                                                                    =
                                                                    let uu____3471
                                                                    =
                                                                    let uu____3482
                                                                    =
                                                                    let uu____3491
                                                                    =
                                                                    let uu____3492
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3492
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3491,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3493
                                                                    =
                                                                    let uu____3504
                                                                    =
                                                                    let uu____3515
                                                                    =
                                                                    let uu____3524
                                                                    =
                                                                    let uu____3525
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3525
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3524,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3526
                                                                    =
                                                                    let uu____3537
                                                                    =
                                                                    let uu____3546
                                                                    =
                                                                    let uu____3547
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3547
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3546,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3548
                                                                    =
                                                                    let uu____3559
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
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3568,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3570
                                                                    =
                                                                    let uu____3581
                                                                    =
                                                                    let uu____3592
                                                                    =
                                                                    let uu____3603
                                                                    =
                                                                    let uu____3612
                                                                    =
                                                                    let uu____3613
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3613
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3612,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3614
                                                                    =
                                                                    let uu____3625
                                                                    =
                                                                    let uu____3634
                                                                    =
                                                                    let uu____3635
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3635
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3634,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3636
                                                                    =
                                                                    let uu____3647
                                                                    =
                                                                    let uu____3656
                                                                    =
                                                                    let uu____3657
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3657
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3656,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3658
                                                                    =
                                                                    let uu____3669
                                                                    =
                                                                    let uu____3678
                                                                    =
                                                                    let uu____3679
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3679
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3678,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3680
                                                                    =
                                                                    let uu____3691
                                                                    =
                                                                    let uu____3700
                                                                    =
                                                                    let uu____3701
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3701
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3700,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3702
                                                                    =
                                                                    let uu____3713
                                                                    =
                                                                    let uu____3722
                                                                    =
                                                                    let uu____3723
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3723
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3722,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3724
                                                                    =
                                                                    let uu____3735
                                                                    =
                                                                    let uu____3744
                                                                    =
                                                                    let uu____3745
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3745
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3744,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3746
                                                                    =
                                                                    let uu____3757
                                                                    =
                                                                    let uu____3766
                                                                    =
                                                                    let uu____3767
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3767
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3766,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3768
                                                                    =
                                                                    let uu____3779
                                                                    =
                                                                    let uu____3788
                                                                    =
                                                                    let uu____3789
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3789
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3788,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3790
                                                                    =
                                                                    let uu____3801
                                                                    =
                                                                    let uu____3812
                                                                    =
                                                                    let uu____3821
                                                                    =
                                                                    let uu____3822
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3822
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3821,
                                                                    " ")  in
                                                                    let uu____3823
                                                                    =
                                                                    let uu____3834
                                                                    =
                                                                    let uu____3845
                                                                    =
                                                                    let uu____3856
                                                                    =
                                                                    let uu____3867
                                                                    =
                                                                    let uu____3878
                                                                    =
                                                                    let uu____3887
                                                                    =
                                                                    let uu____3888
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3888
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____3887,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____3889
                                                                    =
                                                                    let uu____3900
                                                                    =
                                                                    let uu____3909
                                                                    =
                                                                    let uu____3910
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3910
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3909,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____3911
                                                                    =
                                                                    let uu____3922
                                                                    =
                                                                    let uu____3933
                                                                    =
                                                                    let uu____3942
                                                                    =
                                                                    let uu____3943
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3943
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3942,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____3944
                                                                    =
                                                                    let uu____3955
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
                                                                    "trace_error",
                                                                    uu____3964,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____3966
                                                                    =
                                                                    let uu____3977
                                                                    =
                                                                    let uu____3986
                                                                    =
                                                                    let uu____3987
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3987
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____3986,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____3988
                                                                    =
                                                                    let uu____3999
                                                                    =
                                                                    let uu____4008
                                                                    =
                                                                    let uu____4009
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4009
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4008,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4010
                                                                    =
                                                                    let uu____4021
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
                                                                    "unsafe_tactic_exec",
                                                                    uu____4030,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4032
                                                                    =
                                                                    let uu____4043
                                                                    =
                                                                    let uu____4052
                                                                    =
                                                                    let uu____4053
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4053
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4052,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4054
                                                                    =
                                                                    let uu____4065
                                                                    =
                                                                    let uu____4074
                                                                    =
                                                                    let uu____4075
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4075
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4074,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4076
                                                                    =
                                                                    let uu____4087
                                                                    =
                                                                    let uu____4096
                                                                    =
                                                                    let uu____4097
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4097
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4096,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4098
                                                                    =
                                                                    let uu____4109
                                                                    =
                                                                    let uu____4120
                                                                    =
                                                                    let uu____4129
                                                                    =
                                                                    let uu____4130
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4130
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4129,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4131
                                                                    =
                                                                    let uu____4142
                                                                    =
                                                                    let uu____4153
                                                                    =
                                                                    let uu____4164
                                                                    =
                                                                    let uu____4175
                                                                    =
                                                                    let uu____4184
                                                                    =
                                                                    let uu____4185
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4185
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4184,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4186
                                                                    =
                                                                    let uu____4197
                                                                    =
                                                                    let uu____4207
                                                                    =
                                                                    let uu____4208
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
                                                                    ((fun
                                                                    uu____4223
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4216)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4208
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4207,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4227
                                                                    =
                                                                    let uu____4239
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
                                                                    "warn_default_effects",
                                                                    uu____4248,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4250
                                                                    =
                                                                    let uu____4261
                                                                    =
                                                                    let uu____4272
                                                                    =
                                                                    let uu____4281
                                                                    =
                                                                    let uu____4282
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4282
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4281,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4283
                                                                    =
                                                                    let uu____4294
                                                                    =
                                                                    let uu____4305
                                                                    =
                                                                    let uu____4316
                                                                    =
                                                                    let uu____4327
                                                                    =
                                                                    let uu____4338
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
                                                                    "__no_positivity",
                                                                    uu____4347,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4349
                                                                    =
                                                                    let uu____4360
                                                                    =
                                                                    let uu____4369
                                                                    =
                                                                    let uu____4370
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4370
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4369,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4371
                                                                    =
                                                                    let uu____4382
                                                                    =
                                                                    let uu____4393
                                                                    =
                                                                    let uu____4402
                                                                    =
                                                                    let uu____4403
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4403
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    uu____4402,
                                                                    "Extract interfaces from the dependencies and use them for verification")
                                                                     in
                                                                    let uu____4404
                                                                    =
                                                                    let uu____4415
                                                                    =
                                                                    let uu____4425
                                                                    =
                                                                    let uu____4426
                                                                    =
                                                                    let uu____4434
                                                                    =
                                                                    let uu____4435
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4435
                                                                     in
                                                                    ((fun
                                                                    uu____4441
                                                                     ->
                                                                    (
                                                                    let uu____4443
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4443);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4434)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4426
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4425,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4415]
                                                                     in
                                                                    uu____4393
                                                                    ::
                                                                    uu____4404
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4382
                                                                     in
                                                                    uu____4360
                                                                    ::
                                                                    uu____4371
                                                                     in
                                                                    uu____4338
                                                                    ::
                                                                    uu____4349
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'false')")
                                                                    ::
                                                                    uu____4327
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4316
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4305
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4294
                                                                     in
                                                                    uu____4272
                                                                    ::
                                                                    uu____4283
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4261
                                                                     in
                                                                    uu____4239
                                                                    ::
                                                                    uu____4250
                                                                     in
                                                                    uu____4197
                                                                    ::
                                                                    uu____4227
                                                                     in
                                                                    uu____4175
                                                                    ::
                                                                    uu____4186
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4164
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4153
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4142
                                                                     in
                                                                    uu____4120
                                                                    ::
                                                                    uu____4131
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4109
                                                                     in
                                                                    uu____4087
                                                                    ::
                                                                    uu____4098
                                                                     in
                                                                    uu____4065
                                                                    ::
                                                                    uu____4076
                                                                     in
                                                                    uu____4043
                                                                    ::
                                                                    uu____4054
                                                                     in
                                                                    uu____4021
                                                                    ::
                                                                    uu____4032
                                                                     in
                                                                    uu____3999
                                                                    ::
                                                                    uu____4010
                                                                     in
                                                                    uu____3977
                                                                    ::
                                                                    uu____3988
                                                                     in
                                                                    uu____3955
                                                                    ::
                                                                    uu____3966
                                                                     in
                                                                    uu____3933
                                                                    ::
                                                                    uu____3944
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3922
                                                                     in
                                                                    uu____3900
                                                                    ::
                                                                    uu____3911
                                                                     in
                                                                    uu____3878
                                                                    ::
                                                                    uu____3889
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3867
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3856
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3845
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3834
                                                                     in
                                                                    uu____3812
                                                                    ::
                                                                    uu____3823
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3801
                                                                     in
                                                                    uu____3779
                                                                    ::
                                                                    uu____3790
                                                                     in
                                                                    uu____3757
                                                                    ::
                                                                    uu____3768
                                                                     in
                                                                    uu____3735
                                                                    ::
                                                                    uu____3746
                                                                     in
                                                                    uu____3713
                                                                    ::
                                                                    uu____3724
                                                                     in
                                                                    uu____3691
                                                                    ::
                                                                    uu____3702
                                                                     in
                                                                    uu____3669
                                                                    ::
                                                                    uu____3680
                                                                     in
                                                                    uu____3647
                                                                    ::
                                                                    uu____3658
                                                                     in
                                                                    uu____3625
                                                                    ::
                                                                    uu____3636
                                                                     in
                                                                    uu____3603
                                                                    ::
                                                                    uu____3614
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3592
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3581
                                                                     in
                                                                    uu____3559
                                                                    ::
                                                                    uu____3570
                                                                     in
                                                                    uu____3537
                                                                    ::
                                                                    uu____3548
                                                                     in
                                                                    uu____3515
                                                                    ::
                                                                    uu____3526
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3504
                                                                     in
                                                                    uu____3482
                                                                    ::
                                                                    uu____3493
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3471
                                                                     in
                                                                    uu____3449
                                                                    ::
                                                                    uu____3460
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3438
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3427
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3416
                                                                     in
                                                                    uu____3394
                                                                    ::
                                                                    uu____3405
                                                                     in
                                                                  uu____3372
                                                                    ::
                                                                    uu____3383
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "load",
                                                                  (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                  "Load compiled module")
                                                                  ::
                                                                  uu____3361
                                                                 in
                                                              uu____3339 ::
                                                                uu____3350
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "initial_ifuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                              :: uu____3328
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "initial_fuel",
                                                            (IntStr
                                                               "non-negative integer"),
                                                            "Number of unrolling of recursive functions to try initially (default 2)")
                                                            :: uu____3317
                                                           in
                                                        uu____3295 ::
                                                          uu____3306
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "include",
                                                        (ReverseAccumulated
                                                           (PathStr "path")),
                                                        "A directory in which to search for files included on the command line")
                                                        :: uu____3284
                                                       in
                                                    uu____3262 :: uu____3273
                                                     in
                                                  uu____3240 :: uu____3251
                                                   in
                                                uu____3218 :: uu____3229  in
                                              (FStar_Getopt.noshort,
                                                "hint_file",
                                                (PathStr "path"),
                                                "Read/write hints to <path> (instead of module-specific hints files)")
                                                :: uu____3207
                                               in
                                            uu____3185 :: uu____3196  in
                                          (FStar_Getopt.noshort,
                                            "fstar_home", (PathStr "dir"),
                                            "Set the FSTAR_HOME variable to <dir>")
                                            :: uu____3174
                                           in
                                        uu____3152 :: uu____3163  in
                                      (FStar_Getopt.noshort,
                                        "extract_namespace",
                                        (Accumulated
                                           (PostProcessed
                                              (pp_lowercase,
                                                (SimpleStr "namespace name")))),
                                        "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                        :: uu____3141
                                       in
                                    (FStar_Getopt.noshort, "extract_module",
                                      (Accumulated
                                         (PostProcessed
                                            (pp_lowercase,
                                              (SimpleStr "module_name")))),
                                      "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                      :: uu____3130
                                     in
                                  (FStar_Getopt.noshort, "extract",
                                    (Accumulated
                                       (SimpleStr
                                          "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                    "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                    :: uu____3119
                                   in
                                uu____3097 :: uu____3108  in
                              (FStar_Getopt.noshort, "dump_module",
                                (Accumulated (SimpleStr "module_name")), "")
                                :: uu____3086
                               in
                            uu____3064 :: uu____3075  in
                          uu____3042 :: uu____3053  in
                        uu____3020 :: uu____3031  in
                      (FStar_Getopt.noshort, "dep",
                        (EnumStr ["make"; "graph"; "full"]),
                        "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                        :: uu____3009
                       in
                    (FStar_Getopt.noshort, "defensive",
                      (EnumStr ["no"; "warn"; "fail"]),
                      "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                      :: uu____2998
                     in
                  (FStar_Getopt.noshort, "debug_level",
                    (Accumulated
                       (OpenEnumStr
                          (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                    "Control the verbosity of debugging info") :: uu____2987
                   in
                (FStar_Getopt.noshort, "debug",
                  (Accumulated (SimpleStr "module_name")),
                  "Print lots of debugging information while checking module")
                  :: uu____2976
                 in
              (FStar_Getopt.noshort, "codegen-lib",
                (Accumulated (SimpleStr "namespace")),
                "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                :: uu____2965
               in
            (FStar_Getopt.noshort, "codegen",
              (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
              "Generate code for further compilation to executable code, or build a compiler plugin")
              :: uu____2954
             in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2943
           in
        uu____2921 :: uu____2932  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2910
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2899

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5203  ->
    let uu____5206 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5231  ->
         match uu____5231 with
         | (short,long,typ,doc) ->
             let uu____5244 =
               let uu____5255 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5255, doc)  in
             mk_spec uu____5244) uu____5206

let (settable : Prims.string -> Prims.bool) =
  fun uu___44_5264  ->
    match uu___44_5264 with
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
    | uu____5265 -> false
  
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
       (fun uu____5324  ->
          match uu____5324 with
          | (uu____5335,x,uu____5337,uu____5338) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5384  ->
          match uu____5384 with
          | (uu____5395,x,uu____5397,uu____5398) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5407  ->
    let uu____5408 = specs ()  in display_usage_aux uu____5408
  
let (fstar_home : unit -> Prims.string) =
  fun uu____5425  ->
    let uu____5426 = get_fstar_home ()  in
    match uu____5426 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir ()  in
        let x1 = Prims.strcat x "/.."  in
        ((let uu____5432 =
            let uu____5437 = mk_string x1  in ("fstar_home", uu____5437)  in
          set_option' uu____5432);
         x1)
    | FStar_Pervasives_Native.Some x -> x
  
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5447 -> true
    | uu____5448 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5455 -> uu____5455
  
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
          let uu____5503 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5503
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5531  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5536 =
             let uu____5539 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5539 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5536)
       in
    let uu____5596 =
      let uu____5599 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5599
       in
    (res, uu____5596)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____5637  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____5676 = specs ()  in
       FStar_Getopt.parse_cmdline uu____5676 (fun x  -> ())  in
     (let uu____5682 =
        let uu____5687 =
          let uu____5688 = FStar_List.map mk_string old_verify_module  in
          List uu____5688  in
        ("verify_module", uu____5687)  in
      set_option' uu____5682);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____5698 =
        let uu____5699 =
          let uu____5700 =
            let uu____5701 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____5701  in
          (FStar_String.length f1) - uu____5700  in
        uu____5699 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5698  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5707 = get_lax ()  in
    if uu____5707
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____5717 = module_name_of_file_name fn  in should_verify uu____5717
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5723 = get___temp_no_proj ()  in
    FStar_List.contains m uu____5723
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5731 = should_verify m  in
    if uu____5731 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____5739  ->
    let uu____5740 = get_no_default_includes ()  in
    if uu____5740
    then get_include ()
    else
      (let h = fstar_home ()  in
       let defs = universe_include_path_base_dirs  in
       let uu____5748 =
         let uu____5751 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x))
            in
         FStar_All.pipe_right uu____5751
           (FStar_List.filter FStar_Util.file_exists)
          in
       let uu____5764 =
         let uu____5767 = get_include ()  in
         FStar_List.append uu____5767 ["."]  in
       FStar_List.append uu____5748 uu____5764)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun filename  ->
    let uu____5777 = FStar_Util.is_path_absolute filename  in
    if uu____5777
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5784 =
         let uu____5787 = include_path ()  in FStar_List.rev uu____5787  in
       FStar_Util.find_map uu____5784
         (fun p  ->
            let path =
              if p = "." then filename else FStar_Util.join_paths p filename
               in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
  
let (prims : unit -> Prims.string) =
  fun uu____5802  ->
    let uu____5803 = get_prims ()  in
    match uu____5803 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____5807 = find_file filename  in
        (match uu____5807 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5811 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____5811)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____5817  ->
    let uu____5818 = prims ()  in FStar_Util.basename uu____5818
  
let (pervasives : unit -> Prims.string) =
  fun uu____5823  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____5825 = find_file filename  in
    match uu____5825 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5829 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5829
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____5834  ->
    let uu____5835 = pervasives ()  in FStar_Util.basename uu____5835
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____5840  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____5842 = find_file filename  in
    match uu____5842 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5846 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5846
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____5852 = get_odir ()  in
    match uu____5852 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____5861 = get_cache_dir ()  in
    match uu____5861 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____5865 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____5865
  
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
             let uu____5919 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             FStar_Ident.path_of_text uu____5919  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           let uu____5923 = FStar_Ident.path_of_text s1  in
           (uu____5923, true))
       in
    let uu____5924 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____5924 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____5994 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____5994 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6003  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6008  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6015  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6020  -> get_cache_checked_modules () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin [@@deriving show]
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6026 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6032 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6038 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6044 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6051  ->
    let uu____6052 = get_codegen ()  in
    FStar_Util.map_opt uu____6052
      (fun uu___45_6056  ->
         match uu___45_6056 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6057 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6066  ->
    let uu____6067 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6067
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6084  -> let uu____6085 = get_debug ()  in uu____6085 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6095 = get_debug ()  in
    FStar_All.pipe_right uu____6095 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6112 = get_debug ()  in
       FStar_All.pipe_right uu____6112 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6121  -> let uu____6122 = get_defensive ()  in uu____6122 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6127  ->
    let uu____6128 = get_defensive ()  in uu____6128 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6135  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6140  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6145  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6150  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6156 = get_dump_module ()  in
    FStar_All.pipe_right uu____6156 (FStar_List.contains s)
  
let (eager_inference : unit -> Prims.bool) =
  fun uu____6165  -> get_eager_inference () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6170  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6176 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6176
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6210  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6215  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6220  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6227  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6232  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6237  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6242  ->
    let uu____6243 = get_initial_fuel ()  in
    let uu____6244 = get_max_fuel ()  in Prims.min uu____6243 uu____6244
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6249  ->
    let uu____6250 = get_initial_ifuel ()  in
    let uu____6251 = get_max_ifuel ()  in Prims.min uu____6250 uu____6251
  
let (interactive : unit -> Prims.bool) =
  fun uu____6256  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6261  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6268  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6273  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6278  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6283  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6288  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6293  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6298  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6303  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6308  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6313  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6318  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6325 = get_no_extract ()  in
    FStar_All.pipe_right uu____6325
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6336  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6341  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6346  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6353  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6358  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6363  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6368  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6373  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6378  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6383  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6388  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____6393  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____6398  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6405  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____6410  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6415  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6420  ->
    let uu____6421 = get_smtencoding_nl_arith_repr ()  in
    uu____6421 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6426  ->
    let uu____6427 = get_smtencoding_nl_arith_repr ()  in
    uu____6427 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6432  ->
    let uu____6433 = get_smtencoding_nl_arith_repr ()  in
    uu____6433 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6438  ->
    let uu____6439 = get_smtencoding_l_arith_repr ()  in
    uu____6439 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6444  ->
    let uu____6445 = get_smtencoding_l_arith_repr ()  in
    uu____6445 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6450  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6455  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6460  -> get_tactic_trace_d () 
let (timing : unit -> Prims.bool) = fun uu____6465  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____6470  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____6475  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____6480  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____6485  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____6490  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____6495  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6502  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____6507  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____6518  ->
    let uu____6519 = get_using_facts_from ()  in
    match uu____6519 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____6555  ->
    let uu____6556 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____6556
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____6563  ->
    let uu____6564 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____6564 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____6567 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____6574  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____6579  ->
    let uu____6580 = get_smt ()  in
    match uu____6580 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____6590  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____6595  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____6600  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____6605  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____6610  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____6615  -> get_use_two_phase_tc () 
let (no_positivity : unit -> Prims.bool) =
  fun uu____6620  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____6625  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____6630  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____6635  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____6642 = get_extract ()  in
    match uu____6642 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____6653 =
            let uu____6666 = get_no_extract ()  in
            let uu____6669 = get_extract_namespace ()  in
            let uu____6672 = get_extract_module ()  in
            (uu____6666, uu____6669, uu____6672)  in
          match uu____6653 with
          | ([],[],[]) -> ()
          | uu____6687 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = FStar_Ident.path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____6733,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____6752 -> false  in
          let uu____6761 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____6795  ->
                    match uu____6795 with
                    | (path,uu____6803) -> matches_path m_components path))
             in
          match uu____6761 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____6814,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____6834 = get_extract_namespace ()  in
          match uu____6834 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____6850 = get_extract_module ()  in
          match uu____6850 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____6862 = no_extract m1  in Prims.op_Negation uu____6862) &&
          (let uu____6864 =
             let uu____6873 = get_extract_namespace ()  in
             let uu____6876 = get_extract_module ()  in
             (uu____6873, uu____6876)  in
           (match uu____6864 with
            | ([],[]) -> true
            | uu____6887 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  