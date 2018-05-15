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
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1328  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1337  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1346  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1355  -> lookup_opt "debug_level" (as_list as_string) 
let (get_defensive : unit -> Prims.string) =
  fun uu____1362  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1369  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1376  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1381  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1386  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1393  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1400  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1405  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1414  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1427  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1436  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1443  -> lookup_opt "fs_typ_app" as_bool 
let (get_fstar_home : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1450  -> lookup_opt "fstar_home" (as_option as_string) 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1457  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1462  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1469  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1476  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1481  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1488  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1495  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1500  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1505  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1510  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1517  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1524  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1529  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1534  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1539  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1544  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1549  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1554  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1559  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1566  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1573  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1578  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1583  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1590  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1597  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1604  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1611  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1616  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1621  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1626  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1631  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1636  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1641  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1646  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1651  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1658  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1665  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1672  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1679  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1684  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1689  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1694  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1699  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1704  -> lookup_opt "tactic_trace_d" as_int 
let (get_timing : unit -> Prims.bool) =
  fun uu____1709  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1714  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1719  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1724  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1729  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1734  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1739  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1746  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1753  ->
    let uu____1754 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1754
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1763  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1776  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1785  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1794  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1801  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1806  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1813  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1820  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1825  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1830  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1835  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1840  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1845  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1850  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1855  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1860  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___70_1865  ->
    match uu___70_1865 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1877 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1883 = get_debug_level ()  in
    FStar_All.pipe_right uu____1883
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2016  ->
    let uu____2017 =
      let uu____2018 = FStar_ST.op_Bang _version  in
      let uu____2042 = FStar_ST.op_Bang _platform  in
      let uu____2066 = FStar_ST.op_Bang _compiler  in
      let uu____2090 = FStar_ST.op_Bang _date  in
      let uu____2114 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2018
        uu____2042 uu____2066 uu____2090 uu____2114
       in
    FStar_Util.print_string uu____2017
  
let display_usage_aux :
  'Auu____2144 'Auu____2145 .
    ('Auu____2144,Prims.string,'Auu____2145 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2193  ->
         match uu____2193 with
         | (uu____2204,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2216 =
                      let uu____2217 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2217  in
                    FStar_Util.print_string uu____2216
                  else
                    (let uu____2219 =
                       let uu____2220 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2220 doc  in
                     FStar_Util.print_string uu____2219)
              | FStar_Getopt.OneArg (uu____2221,argname) ->
                  if doc = ""
                  then
                    let uu____2229 =
                      let uu____2230 = FStar_Util.colorize_bold flag  in
                      let uu____2231 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2230 uu____2231
                       in
                    FStar_Util.print_string uu____2229
                  else
                    (let uu____2233 =
                       let uu____2234 = FStar_Util.colorize_bold flag  in
                       let uu____2235 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2234
                         uu____2235 doc
                        in
                     FStar_Util.print_string uu____2233))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2263 = o  in
    match uu____2263 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2299 =
                let uu____2300 = f ()  in set_option name uu____2300  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2315 = f x  in set_option name uu____2315
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2335 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2335  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2358 =
        let uu____2361 = lookup_opt name as_list'  in
        FStar_List.append uu____2361 [value]  in
      mk_list uu____2358
  
let accumulate_string :
  'Auu____2374 .
    Prims.string -> ('Auu____2374 -> Prims.string) -> 'Auu____2374 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2395 =
          let uu____2396 =
            let uu____2397 = post_processor value  in mk_string uu____2397
             in
          accumulated_option name uu____2396  in
        set_option name uu____2395
  
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
    match projectee with | Const _0 -> true | uu____2493 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2507 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2520 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2527 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2541 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2557 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2583 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2622 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2657 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2671 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2692 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2730 -> true
    | uu____2731 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2738 -> uu____2738
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2758 ->
              let uu____2759 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2759 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2763 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2763
          | PathStr uu____2766 -> mk_path str_val
          | SimpleStr uu____2767 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2772 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2787 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2787
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
            let uu____2806 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2806
  
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
    | PostProcessed (uu____2843,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2853,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2880 = desc_of_opt_type typ  in
      match uu____2880 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2886  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2903 =
      let uu____2904 = as_string s  in FStar_String.lowercase uu____2904  in
    mk_string uu____2903
  
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2926  ->
    let uu____2938 =
      let uu____2950 =
        let uu____2962 =
          let uu____2972 = let uu____2973 = mk_bool true  in Const uu____2973
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2972,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
           in
        let uu____2975 =
          let uu____2987 =
            let uu____2999 =
              let uu____3011 =
                let uu____3023 =
                  let uu____3035 =
                    let uu____3047 =
                      let uu____3059 =
                        let uu____3071 =
                          let uu____3081 =
                            let uu____3082 = mk_bool true  in
                            Const uu____3082  in
                          (FStar_Getopt.noshort, "detail_errors", uu____3081,
                            "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                           in
                        let uu____3084 =
                          let uu____3096 =
                            let uu____3106 =
                              let uu____3107 = mk_bool true  in
                              Const uu____3107  in
                            (FStar_Getopt.noshort, "detail_hint_replay",
                              uu____3106,
                              "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                             in
                          let uu____3109 =
                            let uu____3121 =
                              let uu____3131 =
                                let uu____3132 = mk_bool true  in
                                Const uu____3132  in
                              (FStar_Getopt.noshort, "doc", uu____3131,
                                "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                               in
                            let uu____3134 =
                              let uu____3146 =
                                let uu____3158 =
                                  let uu____3168 =
                                    let uu____3169 = mk_bool true  in
                                    Const uu____3169  in
                                  (FStar_Getopt.noshort, "eager_inference",
                                    uu____3168,
                                    "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                   in
                                let uu____3171 =
                                  let uu____3183 =
                                    let uu____3193 =
                                      let uu____3194 = mk_bool true  in
                                      Const uu____3194  in
                                    (FStar_Getopt.noshort, "eager_subtyping",
                                      uu____3193,
                                      "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                     in
                                  let uu____3196 =
                                    let uu____3208 =
                                      let uu____3220 =
                                        let uu____3232 =
                                          let uu____3244 =
                                            let uu____3254 =
                                              let uu____3255 = mk_bool true
                                                 in
                                              Const uu____3255  in
                                            (FStar_Getopt.noshort,
                                              "expose_interfaces",
                                              uu____3254,
                                              "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                             in
                                          let uu____3257 =
                                            let uu____3269 =
                                              let uu____3281 =
                                                let uu____3291 =
                                                  let uu____3292 =
                                                    mk_bool true  in
                                                  Const uu____3292  in
                                                (FStar_Getopt.noshort,
                                                  "hide_uvar_nums",
                                                  uu____3291,
                                                  "Don't print unification variable numbers")
                                                 in
                                              let uu____3294 =
                                                let uu____3306 =
                                                  let uu____3318 =
                                                    let uu____3328 =
                                                      let uu____3329 =
                                                        mk_bool true  in
                                                      Const uu____3329  in
                                                    (FStar_Getopt.noshort,
                                                      "hint_info",
                                                      uu____3328,
                                                      "Print information regarding hints (deprecated; use --query_stats instead)")
                                                     in
                                                  let uu____3331 =
                                                    let uu____3343 =
                                                      let uu____3353 =
                                                        let uu____3354 =
                                                          mk_bool true  in
                                                        Const uu____3354  in
                                                      (FStar_Getopt.noshort,
                                                        "in", uu____3353,
                                                        "Legacy interactive mode; reads input from stdin")
                                                       in
                                                    let uu____3356 =
                                                      let uu____3368 =
                                                        let uu____3378 =
                                                          let uu____3379 =
                                                            mk_bool true  in
                                                          Const uu____3379
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "ide", uu____3378,
                                                          "JSON-based interactive mode for IDEs")
                                                         in
                                                      let uu____3381 =
                                                        let uu____3393 =
                                                          let uu____3405 =
                                                            let uu____3415 =
                                                              let uu____3416
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____3416
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "indent",
                                                              uu____3415,
                                                              "Parses and outputs the files on the command line")
                                                             in
                                                          let uu____3418 =
                                                            let uu____3430 =
                                                              let uu____3442
                                                                =
                                                                let uu____3454
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
                                                                    "lax",
                                                                    uu____3464,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                   in
                                                                let uu____3467
                                                                  =
                                                                  let uu____3479
                                                                    =
                                                                    let uu____3491
                                                                    =
                                                                    let uu____3501
                                                                    =
                                                                    let uu____3502
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3502
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3501,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3504
                                                                    =
                                                                    let uu____3516
                                                                    =
                                                                    let uu____3526
                                                                    =
                                                                    let uu____3527
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3527
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3526,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3529
                                                                    =
                                                                    let uu____3541
                                                                    =
                                                                    let uu____3553
                                                                    =
                                                                    let uu____3565
                                                                    =
                                                                    let uu____3577
                                                                    =
                                                                    let uu____3587
                                                                    =
                                                                    let uu____3588
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3588
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3587,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3590
                                                                    =
                                                                    let uu____3602
                                                                    =
                                                                    let uu____3614
                                                                    =
                                                                    let uu____3624
                                                                    =
                                                                    let uu____3625
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3625
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3624,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3627
                                                                    =
                                                                    let uu____3639
                                                                    =
                                                                    let uu____3651
                                                                    =
                                                                    let uu____3661
                                                                    =
                                                                    let uu____3662
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3662
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3661,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3664
                                                                    =
                                                                    let uu____3676
                                                                    =
                                                                    let uu____3686
                                                                    =
                                                                    let uu____3687
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3687
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3686,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3689
                                                                    =
                                                                    let uu____3701
                                                                    =
                                                                    let uu____3711
                                                                    =
                                                                    let uu____3712
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3712
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3711,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3714
                                                                    =
                                                                    let uu____3726
                                                                    =
                                                                    let uu____3738
                                                                    =
                                                                    let uu____3750
                                                                    =
                                                                    let uu____3760
                                                                    =
                                                                    let uu____3761
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3761
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3760,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3763
                                                                    =
                                                                    let uu____3775
                                                                    =
                                                                    let uu____3785
                                                                    =
                                                                    let uu____3786
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3786
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3785,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3788
                                                                    =
                                                                    let uu____3800
                                                                    =
                                                                    let uu____3810
                                                                    =
                                                                    let uu____3811
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3811
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3810,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3813
                                                                    =
                                                                    let uu____3825
                                                                    =
                                                                    let uu____3835
                                                                    =
                                                                    let uu____3836
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3836
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3835,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3838
                                                                    =
                                                                    let uu____3850
                                                                    =
                                                                    let uu____3860
                                                                    =
                                                                    let uu____3861
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3861
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3860,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3863
                                                                    =
                                                                    let uu____3875
                                                                    =
                                                                    let uu____3885
                                                                    =
                                                                    let uu____3886
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3886
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3885,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3888
                                                                    =
                                                                    let uu____3900
                                                                    =
                                                                    let uu____3910
                                                                    =
                                                                    let uu____3911
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3911
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3910,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3913
                                                                    =
                                                                    let uu____3925
                                                                    =
                                                                    let uu____3935
                                                                    =
                                                                    let uu____3936
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3936
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3935,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3938
                                                                    =
                                                                    let uu____3950
                                                                    =
                                                                    let uu____3960
                                                                    =
                                                                    let uu____3961
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3961
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3960,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3963
                                                                    =
                                                                    let uu____3975
                                                                    =
                                                                    let uu____3987
                                                                    =
                                                                    let uu____3997
                                                                    =
                                                                    let uu____3998
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3998
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3997,
                                                                    " ")  in
                                                                    let uu____4000
                                                                    =
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
                                                                    let uu____4070
                                                                    =
                                                                    let uu____4071
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4071
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4070,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4073
                                                                    =
                                                                    let uu____4085
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
                                                                    "tactic_trace",
                                                                    uu____4095,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4098
                                                                    =
                                                                    let uu____4110
                                                                    =
                                                                    let uu____4122
                                                                    =
                                                                    let uu____4132
                                                                    =
                                                                    let uu____4133
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4133
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4132,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4135
                                                                    =
                                                                    let uu____4147
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
                                                                    "trace_error",
                                                                    uu____4157,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4160
                                                                    =
                                                                    let uu____4172
                                                                    =
                                                                    let uu____4182
                                                                    =
                                                                    let uu____4183
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4183
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4182,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4185
                                                                    =
                                                                    let uu____4197
                                                                    =
                                                                    let uu____4207
                                                                    =
                                                                    let uu____4208
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4208
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4207,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4210
                                                                    =
                                                                    let uu____4222
                                                                    =
                                                                    let uu____4232
                                                                    =
                                                                    let uu____4233
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4233
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4232,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4235
                                                                    =
                                                                    let uu____4247
                                                                    =
                                                                    let uu____4257
                                                                    =
                                                                    let uu____4258
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4258
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4257,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4260
                                                                    =
                                                                    let uu____4272
                                                                    =
                                                                    let uu____4282
                                                                    =
                                                                    let uu____4283
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4283
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4282,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4285
                                                                    =
                                                                    let uu____4297
                                                                    =
                                                                    let uu____4307
                                                                    =
                                                                    let uu____4308
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4308
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4307,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4310
                                                                    =
                                                                    let uu____4322
                                                                    =
                                                                    let uu____4334
                                                                    =
                                                                    let uu____4344
                                                                    =
                                                                    let uu____4345
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4345
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4344,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4347
                                                                    =
                                                                    let uu____4359
                                                                    =
                                                                    let uu____4371
                                                                    =
                                                                    let uu____4383
                                                                    =
                                                                    let uu____4395
                                                                    =
                                                                    let uu____4405
                                                                    =
                                                                    let uu____4406
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4406
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4405,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4408
                                                                    =
                                                                    let uu____4420
                                                                    =
                                                                    let uu____4430
                                                                    =
                                                                    let uu____4431
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
                                                                    ((fun
                                                                    uu____4446
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4439)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4431
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4430,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4450
                                                                    =
                                                                    let uu____4462
                                                                    =
                                                                    let uu____4472
                                                                    =
                                                                    let uu____4473
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4473
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4472,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4475
                                                                    =
                                                                    let uu____4487
                                                                    =
                                                                    let uu____4499
                                                                    =
                                                                    let uu____4509
                                                                    =
                                                                    let uu____4510
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4510
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4509,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4512
                                                                    =
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
                                                                    let uu____4582
                                                                    =
                                                                    let uu____4583
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4583
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4582,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4585
                                                                    =
                                                                    let uu____4597
                                                                    =
                                                                    let uu____4607
                                                                    =
                                                                    let uu____4608
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4608
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4607,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4610
                                                                    =
                                                                    let uu____4622
                                                                    =
                                                                    let uu____4634
                                                                    =
                                                                    let uu____4646
                                                                    =
                                                                    let uu____4656
                                                                    =
                                                                    let uu____4657
                                                                    =
                                                                    let uu____4665
                                                                    =
                                                                    let uu____4666
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4666
                                                                     in
                                                                    ((fun
                                                                    uu____4672
                                                                     ->
                                                                    (
                                                                    let uu____4674
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4674);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4665)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4657
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4656,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4646]
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4634
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4622
                                                                     in
                                                                    uu____4597
                                                                    ::
                                                                    uu____4610
                                                                     in
                                                                    uu____4572
                                                                    ::
                                                                    uu____4585
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4560
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4548
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4536
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4524
                                                                     in
                                                                    uu____4499
                                                                    ::
                                                                    uu____4512
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4487
                                                                     in
                                                                    uu____4462
                                                                    ::
                                                                    uu____4475
                                                                     in
                                                                    uu____4420
                                                                    ::
                                                                    uu____4450
                                                                     in
                                                                    uu____4395
                                                                    ::
                                                                    uu____4408
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4383
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4371
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4359
                                                                     in
                                                                    uu____4334
                                                                    ::
                                                                    uu____4347
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4322
                                                                     in
                                                                    uu____4297
                                                                    ::
                                                                    uu____4310
                                                                     in
                                                                    uu____4272
                                                                    ::
                                                                    uu____4285
                                                                     in
                                                                    uu____4247
                                                                    ::
                                                                    uu____4260
                                                                     in
                                                                    uu____4222
                                                                    ::
                                                                    uu____4235
                                                                     in
                                                                    uu____4197
                                                                    ::
                                                                    uu____4210
                                                                     in
                                                                    uu____4172
                                                                    ::
                                                                    uu____4185
                                                                     in
                                                                    uu____4147
                                                                    ::
                                                                    uu____4160
                                                                     in
                                                                    uu____4122
                                                                    ::
                                                                    uu____4135
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4110
                                                                     in
                                                                    uu____4085
                                                                    ::
                                                                    uu____4098
                                                                     in
                                                                    uu____4060
                                                                    ::
                                                                    uu____4073
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4048
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4036
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4024
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4012
                                                                     in
                                                                    uu____3987
                                                                    ::
                                                                    uu____4000
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3975
                                                                     in
                                                                    uu____3950
                                                                    ::
                                                                    uu____3963
                                                                     in
                                                                    uu____3925
                                                                    ::
                                                                    uu____3938
                                                                     in
                                                                    uu____3900
                                                                    ::
                                                                    uu____3913
                                                                     in
                                                                    uu____3875
                                                                    ::
                                                                    uu____3888
                                                                     in
                                                                    uu____3850
                                                                    ::
                                                                    uu____3863
                                                                     in
                                                                    uu____3825
                                                                    ::
                                                                    uu____3838
                                                                     in
                                                                    uu____3800
                                                                    ::
                                                                    uu____3813
                                                                     in
                                                                    uu____3775
                                                                    ::
                                                                    uu____3788
                                                                     in
                                                                    uu____3750
                                                                    ::
                                                                    uu____3763
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3738
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3726
                                                                     in
                                                                    uu____3701
                                                                    ::
                                                                    uu____3714
                                                                     in
                                                                    uu____3676
                                                                    ::
                                                                    uu____3689
                                                                     in
                                                                    uu____3651
                                                                    ::
                                                                    uu____3664
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3639
                                                                     in
                                                                    uu____3614
                                                                    ::
                                                                    uu____3627
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3602
                                                                     in
                                                                    uu____3577
                                                                    ::
                                                                    uu____3590
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3565
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3553
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3541
                                                                     in
                                                                    uu____3516
                                                                    ::
                                                                    uu____3529
                                                                     in
                                                                    uu____3491
                                                                    ::
                                                                    uu____3504
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (
                                                                    ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3479
                                                                   in
                                                                uu____3454 ::
                                                                  uu____3467
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_ifuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                :: uu____3442
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "initial_fuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of recursive functions to try initially (default 2)")
                                                              :: uu____3430
                                                             in
                                                          uu____3405 ::
                                                            uu____3418
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "include",
                                                          (ReverseAccumulated
                                                             (PathStr "path")),
                                                          "A directory in which to search for files included on the command line")
                                                          :: uu____3393
                                                         in
                                                      uu____3368 ::
                                                        uu____3381
                                                       in
                                                    uu____3343 :: uu____3356
                                                     in
                                                  uu____3318 :: uu____3331
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "hint_file",
                                                  (PathStr "path"),
                                                  "Read/write hints to <path> (instead of module-specific hints files)")
                                                  :: uu____3306
                                                 in
                                              uu____3281 :: uu____3294  in
                                            (FStar_Getopt.noshort,
                                              "fstar_home", (PathStr "dir"),
                                              "Set the FSTAR_HOME variable to <dir>")
                                              :: uu____3269
                                             in
                                          uu____3244 :: uu____3257  in
                                        (FStar_Getopt.noshort,
                                          "extract_namespace",
                                          (Accumulated
                                             (PostProcessed
                                                (pp_lowercase,
                                                  (SimpleStr "namespace name")))),
                                          "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                          :: uu____3232
                                         in
                                      (FStar_Getopt.noshort,
                                        "extract_module",
                                        (Accumulated
                                           (PostProcessed
                                              (pp_lowercase,
                                                (SimpleStr "module_name")))),
                                        "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                        :: uu____3220
                                       in
                                    (FStar_Getopt.noshort, "extract",
                                      (Accumulated
                                         (SimpleStr
                                            "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                      "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                      :: uu____3208
                                     in
                                  uu____3183 :: uu____3196  in
                                uu____3158 :: uu____3171  in
                              (FStar_Getopt.noshort, "dump_module",
                                (Accumulated (SimpleStr "module_name")), "")
                                :: uu____3146
                               in
                            uu____3121 :: uu____3134  in
                          uu____3096 :: uu____3109  in
                        uu____3071 :: uu____3084  in
                      (FStar_Getopt.noshort, "dep",
                        (EnumStr ["make"; "graph"; "full"]),
                        "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                        :: uu____3059
                       in
                    (FStar_Getopt.noshort, "defensive",
                      (EnumStr ["no"; "warn"; "fail"]),
                      "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                      :: uu____3047
                     in
                  (FStar_Getopt.noshort, "debug_level",
                    (Accumulated
                       (OpenEnumStr
                          (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                    "Control the verbosity of debugging info") :: uu____3035
                   in
                (FStar_Getopt.noshort, "debug",
                  (Accumulated (SimpleStr "module_name")),
                  "Print lots of debugging information while checking module")
                  :: uu____3023
                 in
              (FStar_Getopt.noshort, "codegen-lib",
                (Accumulated (SimpleStr "namespace")),
                "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                :: uu____3011
               in
            (FStar_Getopt.noshort, "codegen",
              (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
              "Generate code for further compilation to executable code, or build a compiler plugin")
              :: uu____2999
             in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2987
           in
        uu____2962 :: uu____2975  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2950
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2938

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5576  ->
    let uu____5579 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5606  ->
         match uu____5606 with
         | (short,long,typ,doc) ->
             let uu____5622 =
               let uu____5634 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5634, doc)  in
             mk_spec uu____5622) uu____5579

let (settable : Prims.string -> Prims.bool) =
  fun uu___71_5644  ->
    match uu___71_5644 with
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
    | uu____5645 -> false
  
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
       (fun uu____5719  ->
          match uu____5719 with
          | (uu____5731,x,uu____5733,uu____5734) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5796  ->
          match uu____5796 with
          | (uu____5808,x,uu____5810,uu____5811) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5822  ->
    let uu____5823 = specs ()  in display_usage_aux uu____5823
  
let (fstar_home : unit -> Prims.string) =
  fun uu____5842  ->
    let uu____5843 = get_fstar_home ()  in
    match uu____5843 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir ()  in
        let x1 = Prims.strcat x "/.."  in
        ((let uu____5849 =
            let uu____5854 = mk_string x1  in ("fstar_home", uu____5854)  in
          set_option' uu____5849);
         x1)
    | FStar_Pervasives_Native.Some x -> x
  
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5865 -> true
    | uu____5866 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5873 -> uu____5873
  
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
          let uu____5901 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5901
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5929  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5934 =
             let uu____5937 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5937 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5934)
       in
    let uu____5994 =
      let uu____5997 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5997
       in
    (res, uu____5994)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6035  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6074 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6074 (fun x  -> ())  in
     (let uu____6080 =
        let uu____6085 =
          let uu____6086 = FStar_List.map mk_string old_verify_module  in
          List uu____6086  in
        ("verify_module", uu____6085)  in
      set_option' uu____6080);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6096 =
        let uu____6097 =
          let uu____6098 =
            let uu____6099 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6099  in
          (FStar_String.length f1) - uu____6098  in
        uu____6097 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6096  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6105 = get_lax ()  in
    if uu____6105
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6115 = module_name_of_file_name fn  in should_verify uu____6115
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6121 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6121
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6129 = should_verify m  in
    if uu____6129 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6137  ->
    let uu____6138 = get_no_default_includes ()  in
    if uu____6138
    then get_include ()
    else
      (let h = fstar_home ()  in
       let defs = universe_include_path_base_dirs  in
       let uu____6146 =
         let uu____6149 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x))
            in
         FStar_All.pipe_right uu____6149
           (FStar_List.filter FStar_Util.file_exists)
          in
       let uu____6162 =
         let uu____6165 = get_include ()  in
         FStar_List.append uu____6165 ["."]  in
       FStar_List.append uu____6146 uu____6162)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun filename  ->
    let uu____6175 = FStar_Util.is_path_absolute filename  in
    if uu____6175
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____6182 =
         let uu____6185 = include_path ()  in FStar_List.rev uu____6185  in
       FStar_Util.find_map uu____6182
         (fun p  ->
            let path =
              if p = "." then filename else FStar_Util.join_paths p filename
               in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
  
let (prims : unit -> Prims.string) =
  fun uu____6200  ->
    let uu____6201 = get_prims ()  in
    match uu____6201 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6205 = find_file filename  in
        (match uu____6205 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6209 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6209)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6215  ->
    let uu____6216 = prims ()  in FStar_Util.basename uu____6216
  
let (pervasives : unit -> Prims.string) =
  fun uu____6221  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____6223 = find_file filename  in
    match uu____6223 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____6227 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6227
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6232  ->
    let uu____6233 = pervasives ()  in FStar_Util.basename uu____6233
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6238  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____6240 = find_file filename  in
    match uu____6240 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____6244 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6244
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____6250 = get_odir ()  in
    match uu____6250 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____6259 = get_cache_dir ()  in
    match uu____6259 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6263 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____6263
  
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
             let uu____6311 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             FStar_Ident.path_of_text uu____6311  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           let uu____6315 = FStar_Ident.path_of_text s1  in
           (uu____6315, true))
       in
    let uu____6316 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6316 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6380 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6380 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6389  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6394  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6401  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6406  -> get_cache_checked_modules () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6412 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6418 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6424 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6430 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6437  ->
    let uu____6438 = get_codegen ()  in
    FStar_Util.map_opt uu____6438
      (fun uu___72_6442  ->
         match uu___72_6442 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6443 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6452  ->
    let uu____6453 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6453
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6470  -> let uu____6471 = get_debug ()  in uu____6471 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6481 = get_debug ()  in
    FStar_All.pipe_right uu____6481 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6498 = get_debug ()  in
       FStar_All.pipe_right uu____6498 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6507  -> let uu____6508 = get_defensive ()  in uu____6508 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6513  ->
    let uu____6514 = get_defensive ()  in uu____6514 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6521  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6526  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6531  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6536  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6542 = get_dump_module ()  in
    FStar_All.pipe_right uu____6542 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6551  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6556  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6562 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6562
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6596  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6601  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6606  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6613  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6618  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6623  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6628  ->
    let uu____6629 = get_initial_fuel ()  in
    let uu____6630 = get_max_fuel ()  in Prims.min uu____6629 uu____6630
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6635  ->
    let uu____6636 = get_initial_ifuel ()  in
    let uu____6637 = get_max_ifuel ()  in Prims.min uu____6636 uu____6637
  
let (interactive : unit -> Prims.bool) =
  fun uu____6642  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6647  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6654  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6659  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6664  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6669  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6674  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6679  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6684  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6689  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6694  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6699  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6704  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6711 = get_no_extract ()  in
    FStar_All.pipe_right uu____6711
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6722  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6727  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6732  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6739  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6744  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6749  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6754  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6759  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6764  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6769  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6774  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____6779  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____6784  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6791  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____6796  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6801  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6806  ->
    let uu____6807 = get_smtencoding_nl_arith_repr ()  in
    uu____6807 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6812  ->
    let uu____6813 = get_smtencoding_nl_arith_repr ()  in
    uu____6813 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6818  ->
    let uu____6819 = get_smtencoding_nl_arith_repr ()  in
    uu____6819 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6824  ->
    let uu____6825 = get_smtencoding_l_arith_repr ()  in
    uu____6825 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6830  ->
    let uu____6831 = get_smtencoding_l_arith_repr ()  in
    uu____6831 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6836  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6841  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6846  -> get_tactic_trace_d () 
let (timing : unit -> Prims.bool) = fun uu____6851  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____6856  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____6861  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____6866  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____6871  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____6876  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____6881  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6888  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____6893  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____6904  ->
    let uu____6905 = get_using_facts_from ()  in
    match uu____6905 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____6935  ->
    let uu____6936 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____6936
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____6943  ->
    let uu____6944 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____6944 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____6947 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____6954  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____6959  ->
    let uu____6960 = get_smt ()  in
    match uu____6960 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____6970  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____6975  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____6980  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____6985  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____6990  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____6995  ->
    (get_use_two_phase_tc ()) &&
      (let uu____6997 = lax ()  in Prims.op_Negation uu____6997)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7002  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7007  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7012  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7017  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7024 = get_extract ()  in
    match uu____7024 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7035 =
            let uu____7048 = get_no_extract ()  in
            let uu____7051 = get_extract_namespace ()  in
            let uu____7054 = get_extract_module ()  in
            (uu____7048, uu____7051, uu____7054)  in
          match uu____7035 with
          | ([],[],[]) -> ()
          | uu____7069 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = FStar_Ident.path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7115,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7134 -> false  in
          let uu____7143 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7177  ->
                    match uu____7177 with
                    | (path,uu____7185) -> matches_path m_components path))
             in
          match uu____7143 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____7196,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____7216 = get_extract_namespace ()  in
          match uu____7216 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____7232 = get_extract_module ()  in
          match uu____7232 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____7244 = no_extract m1  in Prims.op_Negation uu____7244) &&
          (let uu____7246 =
             let uu____7255 = get_extract_namespace ()  in
             let uu____7258 = get_extract_module ()  in
             (uu____7255, uu____7258)  in
           (match uu____7246 with
            | ([],[]) -> true
            | uu____7269 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  