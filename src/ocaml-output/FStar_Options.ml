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
  ("use_extracted_interfaces", (Bool true))] 
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
    let uu____2261 = o  in
    match uu____2261 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2294 =
                let uu____2295 = f ()  in set_option name uu____2295  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2310 = f x  in set_option name uu____2310
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2329 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2329  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2352 =
        let uu____2355 = lookup_opt name as_list'  in
        FStar_List.append uu____2355 [value]  in
      mk_list uu____2352
  
let accumulate_string :
  'Auu____2368 .
    Prims.string -> ('Auu____2368 -> Prims.string) -> 'Auu____2368 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2389 =
          let uu____2390 =
            let uu____2391 = post_processor value  in mk_string uu____2391
             in
          accumulated_option name uu____2390  in
        set_option name uu____2389
  
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
    match projectee with | Const _0 -> true | uu____2487 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2501 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2514 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2521 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2535 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2551 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2577 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2616 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2651 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2665 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2686 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2724 -> true
    | uu____2725 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2732 -> uu____2732
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2752 ->
              let uu____2753 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2753 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2757 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2757
          | PathStr uu____2760 -> mk_path str_val
          | SimpleStr uu____2761 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2766 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2781 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2781
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
            let uu____2800 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2800
  
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
    | PostProcessed (uu____2837,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2847,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2874 = desc_of_opt_type typ  in
      match uu____2874 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2880  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2897 =
      let uu____2898 = as_string s  in FStar_String.lowercase uu____2898  in
    mk_string uu____2897
  
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2919  ->
    let uu____2930 =
      let uu____2941 =
        let uu____2952 =
          let uu____2961 = let uu____2962 = mk_bool true  in Const uu____2962
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2961,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
           in
        let uu____2963 =
          let uu____2974 =
            let uu____2985 =
              let uu____2996 =
                let uu____3007 =
                  let uu____3018 =
                    let uu____3029 =
                      let uu____3040 =
                        let uu____3051 =
                          let uu____3060 =
                            let uu____3061 = mk_bool true  in
                            Const uu____3061  in
                          (FStar_Getopt.noshort, "detail_errors", uu____3060,
                            "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                           in
                        let uu____3062 =
                          let uu____3073 =
                            let uu____3082 =
                              let uu____3083 = mk_bool true  in
                              Const uu____3083  in
                            (FStar_Getopt.noshort, "detail_hint_replay",
                              uu____3082,
                              "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                             in
                          let uu____3084 =
                            let uu____3095 =
                              let uu____3104 =
                                let uu____3105 = mk_bool true  in
                                Const uu____3105  in
                              (FStar_Getopt.noshort, "doc", uu____3104,
                                "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                               in
                            let uu____3106 =
                              let uu____3117 =
                                let uu____3128 =
                                  let uu____3137 =
                                    let uu____3138 = mk_bool true  in
                                    Const uu____3138  in
                                  (FStar_Getopt.noshort, "eager_inference",
                                    uu____3137,
                                    "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                   in
                                let uu____3139 =
                                  let uu____3150 =
                                    let uu____3159 =
                                      let uu____3160 = mk_bool true  in
                                      Const uu____3160  in
                                    (FStar_Getopt.noshort, "eager_subtyping",
                                      uu____3159,
                                      "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                     in
                                  let uu____3161 =
                                    let uu____3172 =
                                      let uu____3183 =
                                        let uu____3194 =
                                          let uu____3205 =
                                            let uu____3214 =
                                              let uu____3215 = mk_bool true
                                                 in
                                              Const uu____3215  in
                                            (FStar_Getopt.noshort,
                                              "expose_interfaces",
                                              uu____3214,
                                              "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                             in
                                          let uu____3216 =
                                            let uu____3227 =
                                              let uu____3238 =
                                                let uu____3247 =
                                                  let uu____3248 =
                                                    mk_bool true  in
                                                  Const uu____3248  in
                                                (FStar_Getopt.noshort,
                                                  "hide_uvar_nums",
                                                  uu____3247,
                                                  "Don't print unification variable numbers")
                                                 in
                                              let uu____3249 =
                                                let uu____3260 =
                                                  let uu____3271 =
                                                    let uu____3280 =
                                                      let uu____3281 =
                                                        mk_bool true  in
                                                      Const uu____3281  in
                                                    (FStar_Getopt.noshort,
                                                      "hint_info",
                                                      uu____3280,
                                                      "Print information regarding hints (deprecated; use --query_stats instead)")
                                                     in
                                                  let uu____3282 =
                                                    let uu____3293 =
                                                      let uu____3302 =
                                                        let uu____3303 =
                                                          mk_bool true  in
                                                        Const uu____3303  in
                                                      (FStar_Getopt.noshort,
                                                        "in", uu____3302,
                                                        "Legacy interactive mode; reads input from stdin")
                                                       in
                                                    let uu____3304 =
                                                      let uu____3315 =
                                                        let uu____3324 =
                                                          let uu____3325 =
                                                            mk_bool true  in
                                                          Const uu____3325
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "ide", uu____3324,
                                                          "JSON-based interactive mode for IDEs")
                                                         in
                                                      let uu____3326 =
                                                        let uu____3337 =
                                                          let uu____3348 =
                                                            let uu____3357 =
                                                              let uu____3358
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____3358
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "indent",
                                                              uu____3357,
                                                              "Parses and outputs the files on the command line")
                                                             in
                                                          let uu____3359 =
                                                            let uu____3370 =
                                                              let uu____3381
                                                                =
                                                                let uu____3392
                                                                  =
                                                                  let uu____3401
                                                                    =
                                                                    let uu____3402
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3402
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3401,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                   in
                                                                let uu____3403
                                                                  =
                                                                  let uu____3414
                                                                    =
                                                                    let uu____3425
                                                                    =
                                                                    let uu____3434
                                                                    =
                                                                    let uu____3435
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3435
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3434,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3436
                                                                    =
                                                                    let uu____3447
                                                                    =
                                                                    let uu____3456
                                                                    =
                                                                    let uu____3457
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3457
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3456,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3458
                                                                    =
                                                                    let uu____3469
                                                                    =
                                                                    let uu____3480
                                                                    =
                                                                    let uu____3491
                                                                    =
                                                                    let uu____3502
                                                                    =
                                                                    let uu____3511
                                                                    =
                                                                    let uu____3512
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3512
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3511,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3513
                                                                    =
                                                                    let uu____3524
                                                                    =
                                                                    let uu____3535
                                                                    =
                                                                    let uu____3544
                                                                    =
                                                                    let uu____3545
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3545
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3544,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3546
                                                                    =
                                                                    let uu____3557
                                                                    =
                                                                    let uu____3568
                                                                    =
                                                                    let uu____3577
                                                                    =
                                                                    let uu____3578
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3578
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3577,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3579
                                                                    =
                                                                    let uu____3590
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
                                                                    "no_smt",
                                                                    uu____3599,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3601
                                                                    =
                                                                    let uu____3612
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
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3621,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3623
                                                                    =
                                                                    let uu____3634
                                                                    =
                                                                    let uu____3645
                                                                    =
                                                                    let uu____3656
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
                                                                    "print_bound_var_types",
                                                                    uu____3665,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3667
                                                                    =
                                                                    let uu____3678
                                                                    =
                                                                    let uu____3687
                                                                    =
                                                                    let uu____3688
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3688
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3687,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3689
                                                                    =
                                                                    let uu____3700
                                                                    =
                                                                    let uu____3709
                                                                    =
                                                                    let uu____3710
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3710
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3709,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3711
                                                                    =
                                                                    let uu____3722
                                                                    =
                                                                    let uu____3731
                                                                    =
                                                                    let uu____3732
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3732
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3731,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3733
                                                                    =
                                                                    let uu____3744
                                                                    =
                                                                    let uu____3753
                                                                    =
                                                                    let uu____3754
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3754
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3753,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3755
                                                                    =
                                                                    let uu____3766
                                                                    =
                                                                    let uu____3775
                                                                    =
                                                                    let uu____3776
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3776
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3775,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3777
                                                                    =
                                                                    let uu____3788
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
                                                                    "prn",
                                                                    uu____3797,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3799
                                                                    =
                                                                    let uu____3810
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
                                                                    "query_stats",
                                                                    uu____3819,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3821
                                                                    =
                                                                    let uu____3832
                                                                    =
                                                                    let uu____3841
                                                                    =
                                                                    let uu____3842
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3842
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3841,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3843
                                                                    =
                                                                    let uu____3854
                                                                    =
                                                                    let uu____3865
                                                                    =
                                                                    let uu____3874
                                                                    =
                                                                    let uu____3875
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3875
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3874,
                                                                    " ")  in
                                                                    let uu____3876
                                                                    =
                                                                    let uu____3887
                                                                    =
                                                                    let uu____3898
                                                                    =
                                                                    let uu____3909
                                                                    =
                                                                    let uu____3920
                                                                    =
                                                                    let uu____3931
                                                                    =
                                                                    let uu____3940
                                                                    =
                                                                    let uu____3941
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3941
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____3940,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____3942
                                                                    =
                                                                    let uu____3953
                                                                    =
                                                                    let uu____3962
                                                                    =
                                                                    let uu____3963
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3963
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3962,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____3964
                                                                    =
                                                                    let uu____3975
                                                                    =
                                                                    let uu____3986
                                                                    =
                                                                    let uu____3995
                                                                    =
                                                                    let uu____3996
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3996
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____3995,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____3997
                                                                    =
                                                                    let uu____4008
                                                                    =
                                                                    let uu____4017
                                                                    =
                                                                    let uu____4018
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4018
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4017,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4019
                                                                    =
                                                                    let uu____4030
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
                                                                    "ugly",
                                                                    uu____4039,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4041
                                                                    =
                                                                    let uu____4052
                                                                    =
                                                                    let uu____4061
                                                                    =
                                                                    let uu____4062
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4062
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4061,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4063
                                                                    =
                                                                    let uu____4074
                                                                    =
                                                                    let uu____4083
                                                                    =
                                                                    let uu____4084
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4084
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4083,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4085
                                                                    =
                                                                    let uu____4096
                                                                    =
                                                                    let uu____4105
                                                                    =
                                                                    let uu____4106
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4106
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4105,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4107
                                                                    =
                                                                    let uu____4118
                                                                    =
                                                                    let uu____4127
                                                                    =
                                                                    let uu____4128
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4128
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4127,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4129
                                                                    =
                                                                    let uu____4140
                                                                    =
                                                                    let uu____4149
                                                                    =
                                                                    let uu____4150
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4150
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4149,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4151
                                                                    =
                                                                    let uu____4162
                                                                    =
                                                                    let uu____4173
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
                                                                    "no_tactics",
                                                                    uu____4182,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4184
                                                                    =
                                                                    let uu____4195
                                                                    =
                                                                    let uu____4206
                                                                    =
                                                                    let uu____4217
                                                                    =
                                                                    let uu____4228
                                                                    =
                                                                    let uu____4237
                                                                    =
                                                                    let uu____4238
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4238
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4237,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4239
                                                                    =
                                                                    let uu____4250
                                                                    =
                                                                    let uu____4259
                                                                    =
                                                                    let uu____4260
                                                                    =
                                                                    let uu____4268
                                                                    =
                                                                    let uu____4269
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4269
                                                                     in
                                                                    ((fun
                                                                    uu____4275
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4268)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4260
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4259,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4278
                                                                    =
                                                                    let uu____4289
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
                                                                    "warn_default_effects",
                                                                    uu____4298,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4300
                                                                    =
                                                                    let uu____4311
                                                                    =
                                                                    let uu____4322
                                                                    =
                                                                    let uu____4331
                                                                    =
                                                                    let uu____4332
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4332
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4331,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4333
                                                                    =
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
                                                                    "__no_positivity",
                                                                    uu____4397,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4399
                                                                    =
                                                                    let uu____4410
                                                                    =
                                                                    let uu____4419
                                                                    =
                                                                    let uu____4420
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4420
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4419,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4421
                                                                    =
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
                                                                    let uu____4472
                                                                    =
                                                                    let uu____4473
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4473
                                                                     in
                                                                    ((fun
                                                                    uu____4479
                                                                     ->
                                                                    (
                                                                    let uu____4481
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4481);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4472)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4464
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4463,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4454]
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'true')")
                                                                    ::
                                                                    uu____4443
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4432
                                                                     in
                                                                    uu____4410
                                                                    ::
                                                                    uu____4421
                                                                     in
                                                                    uu____4388
                                                                    ::
                                                                    uu____4399
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4377
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4366
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4355
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4344
                                                                     in
                                                                    uu____4322
                                                                    ::
                                                                    uu____4333
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4311
                                                                     in
                                                                    uu____4289
                                                                    ::
                                                                    uu____4300
                                                                     in
                                                                    uu____4250
                                                                    ::
                                                                    uu____4278
                                                                     in
                                                                    uu____4228
                                                                    ::
                                                                    uu____4239
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4217
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4206
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4195
                                                                     in
                                                                    uu____4173
                                                                    ::
                                                                    uu____4184
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4162
                                                                     in
                                                                    uu____4140
                                                                    ::
                                                                    uu____4151
                                                                     in
                                                                    uu____4118
                                                                    ::
                                                                    uu____4129
                                                                     in
                                                                    uu____4096
                                                                    ::
                                                                    uu____4107
                                                                     in
                                                                    uu____4074
                                                                    ::
                                                                    uu____4085
                                                                     in
                                                                    uu____4052
                                                                    ::
                                                                    uu____4063
                                                                     in
                                                                    uu____4030
                                                                    ::
                                                                    uu____4041
                                                                     in
                                                                    uu____4008
                                                                    ::
                                                                    uu____4019
                                                                     in
                                                                    uu____3986
                                                                    ::
                                                                    uu____3997
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____3975
                                                                     in
                                                                    uu____3953
                                                                    ::
                                                                    uu____3964
                                                                     in
                                                                    uu____3931
                                                                    ::
                                                                    uu____3942
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3920
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3909
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3898
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3887
                                                                     in
                                                                    uu____3865
                                                                    ::
                                                                    uu____3876
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3854
                                                                     in
                                                                    uu____3832
                                                                    ::
                                                                    uu____3843
                                                                     in
                                                                    uu____3810
                                                                    ::
                                                                    uu____3821
                                                                     in
                                                                    uu____3788
                                                                    ::
                                                                    uu____3799
                                                                     in
                                                                    uu____3766
                                                                    ::
                                                                    uu____3777
                                                                     in
                                                                    uu____3744
                                                                    ::
                                                                    uu____3755
                                                                     in
                                                                    uu____3722
                                                                    ::
                                                                    uu____3733
                                                                     in
                                                                    uu____3700
                                                                    ::
                                                                    uu____3711
                                                                     in
                                                                    uu____3678
                                                                    ::
                                                                    uu____3689
                                                                     in
                                                                    uu____3656
                                                                    ::
                                                                    uu____3667
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3645
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3634
                                                                     in
                                                                    uu____3612
                                                                    ::
                                                                    uu____3623
                                                                     in
                                                                    uu____3590
                                                                    ::
                                                                    uu____3601
                                                                     in
                                                                    uu____3568
                                                                    ::
                                                                    uu____3579
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3557
                                                                     in
                                                                    uu____3535
                                                                    ::
                                                                    uu____3546
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3524
                                                                     in
                                                                    uu____3502
                                                                    ::
                                                                    uu____3513
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3491
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3480
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3469
                                                                     in
                                                                    uu____3447
                                                                    ::
                                                                    uu____3458
                                                                     in
                                                                    uu____3425
                                                                    ::
                                                                    uu____3436
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (
                                                                    ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3414
                                                                   in
                                                                uu____3392 ::
                                                                  uu____3403
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_ifuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                :: uu____3381
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "initial_fuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of recursive functions to try initially (default 2)")
                                                              :: uu____3370
                                                             in
                                                          uu____3348 ::
                                                            uu____3359
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "include",
                                                          (ReverseAccumulated
                                                             (PathStr "path")),
                                                          "A directory in which to search for files included on the command line")
                                                          :: uu____3337
                                                         in
                                                      uu____3315 ::
                                                        uu____3326
                                                       in
                                                    uu____3293 :: uu____3304
                                                     in
                                                  uu____3271 :: uu____3282
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "hint_file",
                                                  (PathStr "path"),
                                                  "Read/write hints to <path> (instead of module-specific hints files)")
                                                  :: uu____3260
                                                 in
                                              uu____3238 :: uu____3249  in
                                            (FStar_Getopt.noshort,
                                              "fstar_home", (PathStr "dir"),
                                              "Set the FSTAR_HOME variable to <dir>")
                                              :: uu____3227
                                             in
                                          uu____3205 :: uu____3216  in
                                        (FStar_Getopt.noshort,
                                          "extract_namespace",
                                          (Accumulated
                                             (PostProcessed
                                                (pp_lowercase,
                                                  (SimpleStr "namespace name")))),
                                          "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                          :: uu____3194
                                         in
                                      (FStar_Getopt.noshort,
                                        "extract_module",
                                        (Accumulated
                                           (PostProcessed
                                              (pp_lowercase,
                                                (SimpleStr "module_name")))),
                                        "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                        :: uu____3183
                                       in
                                    (FStar_Getopt.noshort, "extract",
                                      (Accumulated
                                         (SimpleStr
                                            "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                      "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                      :: uu____3172
                                     in
                                  uu____3150 :: uu____3161  in
                                uu____3128 :: uu____3139  in
                              (FStar_Getopt.noshort, "dump_module",
                                (Accumulated (SimpleStr "module_name")), "")
                                :: uu____3117
                               in
                            uu____3095 :: uu____3106  in
                          uu____3073 :: uu____3084  in
                        uu____3051 :: uu____3062  in
                      (FStar_Getopt.noshort, "dep",
                        (EnumStr ["make"; "graph"; "full"]),
                        "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                        :: uu____3040
                       in
                    (FStar_Getopt.noshort, "defensive",
                      (EnumStr ["no"; "warn"; "fail"]),
                      "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                      :: uu____3029
                     in
                  (FStar_Getopt.noshort, "debug_level",
                    (Accumulated
                       (OpenEnumStr
                          (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                    "Control the verbosity of debugging info") :: uu____3018
                   in
                (FStar_Getopt.noshort, "debug",
                  (Accumulated (SimpleStr "module_name")),
                  "Print lots of debugging information while checking module")
                  :: uu____3007
                 in
              (FStar_Getopt.noshort, "codegen-lib",
                (Accumulated (SimpleStr "namespace")),
                "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                :: uu____2996
               in
            (FStar_Getopt.noshort, "codegen",
              (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
              "Generate code for further compilation to executable code, or build a compiler plugin")
              :: uu____2985
             in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2974
           in
        uu____2952 :: uu____2963  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2941
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2930

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5245  ->
    let uu____5248 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5273  ->
         match uu____5273 with
         | (short,long,typ,doc) ->
             let uu____5286 =
               let uu____5297 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5297, doc)  in
             mk_spec uu____5286) uu____5248

let (settable : Prims.string -> Prims.bool) =
  fun uu___71_5306  ->
    match uu___71_5306 with
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
    | uu____5307 -> false
  
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
       (fun uu____5376  ->
          match uu____5376 with
          | (uu____5387,x,uu____5389,uu____5390) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5446  ->
          match uu____5446 with
          | (uu____5457,x,uu____5459,uu____5460) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5469  ->
    let uu____5470 = specs ()  in display_usage_aux uu____5470
  
let (fstar_home : unit -> Prims.string) =
  fun uu____5487  ->
    let uu____5488 = get_fstar_home ()  in
    match uu____5488 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir ()  in
        let x1 = Prims.strcat x "/.."  in
        ((let uu____5494 =
            let uu____5499 = mk_string x1  in ("fstar_home", uu____5499)  in
          set_option' uu____5494);
         x1)
    | FStar_Pervasives_Native.Some x -> x
  
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5510 -> true
    | uu____5511 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5518 -> uu____5518
  
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
          let uu____5546 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5546
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5574  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5579 =
             let uu____5582 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5582 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5579)
       in
    let uu____5639 =
      let uu____5642 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5642
       in
    (res, uu____5639)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____5680  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____5719 = specs ()  in
       FStar_Getopt.parse_cmdline uu____5719 (fun x  -> ())  in
     (let uu____5725 =
        let uu____5730 =
          let uu____5731 = FStar_List.map mk_string old_verify_module  in
          List uu____5731  in
        ("verify_module", uu____5730)  in
      set_option' uu____5725);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____5741 =
        let uu____5742 =
          let uu____5743 =
            let uu____5744 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____5744  in
          (FStar_String.length f1) - uu____5743  in
        uu____5742 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5741  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5750 = get_lax ()  in
    if uu____5750
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____5760 = module_name_of_file_name fn  in should_verify uu____5760
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5766 = get___temp_no_proj ()  in
    FStar_List.contains m uu____5766
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5774 = should_verify m  in
    if uu____5774 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____5782  ->
    let uu____5783 = get_no_default_includes ()  in
    if uu____5783
    then get_include ()
    else
      (let h = fstar_home ()  in
       let defs = universe_include_path_base_dirs  in
       let uu____5791 =
         let uu____5794 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x))
            in
         FStar_All.pipe_right uu____5794
           (FStar_List.filter FStar_Util.file_exists)
          in
       let uu____5807 =
         let uu____5810 = get_include ()  in
         FStar_List.append uu____5810 ["."]  in
       FStar_List.append uu____5791 uu____5807)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun filename  ->
    let uu____5820 = FStar_Util.is_path_absolute filename  in
    if uu____5820
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5827 =
         let uu____5830 = include_path ()  in FStar_List.rev uu____5830  in
       FStar_Util.find_map uu____5827
         (fun p  ->
            let path =
              if p = "." then filename else FStar_Util.join_paths p filename
               in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
  
let (prims : unit -> Prims.string) =
  fun uu____5845  ->
    let uu____5846 = get_prims ()  in
    match uu____5846 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____5850 = find_file filename  in
        (match uu____5850 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5854 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____5854)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____5860  ->
    let uu____5861 = prims ()  in FStar_Util.basename uu____5861
  
let (pervasives : unit -> Prims.string) =
  fun uu____5866  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____5868 = find_file filename  in
    match uu____5868 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5872 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5872
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____5877  ->
    let uu____5878 = pervasives ()  in FStar_Util.basename uu____5878
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____5883  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____5885 = find_file filename  in
    match uu____5885 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5889 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5889
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____5895 = get_odir ()  in
    match uu____5895 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____5904 = get_cache_dir ()  in
    match uu____5904 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____5908 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____5908
  
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
             let uu____5956 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             FStar_Ident.path_of_text uu____5956  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           let uu____5960 = FStar_Ident.path_of_text s1  in
           (uu____5960, true))
       in
    let uu____5961 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____5961 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6025 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6025 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6034  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6039  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6046  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6051  -> get_cache_checked_modules () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6057 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6063 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6069 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6075 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6082  ->
    let uu____6083 = get_codegen ()  in
    FStar_Util.map_opt uu____6083
      (fun uu___72_6087  ->
         match uu___72_6087 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6088 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6097  ->
    let uu____6098 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6098
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6115  -> let uu____6116 = get_debug ()  in uu____6116 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6126 = get_debug ()  in
    FStar_All.pipe_right uu____6126 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6143 = get_debug ()  in
       FStar_All.pipe_right uu____6143 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6152  -> let uu____6153 = get_defensive ()  in uu____6153 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6158  ->
    let uu____6159 = get_defensive ()  in uu____6159 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6166  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6171  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6176  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6181  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6187 = get_dump_module ()  in
    FStar_All.pipe_right uu____6187 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6196  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6201  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6207 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6207
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6241  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6246  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6251  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6258  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6263  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6268  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6273  ->
    let uu____6274 = get_initial_fuel ()  in
    let uu____6275 = get_max_fuel ()  in Prims.min uu____6274 uu____6275
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6280  ->
    let uu____6281 = get_initial_ifuel ()  in
    let uu____6282 = get_max_ifuel ()  in Prims.min uu____6281 uu____6282
  
let (interactive : unit -> Prims.bool) =
  fun uu____6287  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6292  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6299  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6304  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6309  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6314  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6319  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6324  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6329  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6334  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6339  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6344  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6349  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6356 = get_no_extract ()  in
    FStar_All.pipe_right uu____6356
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6367  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6372  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6377  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6384  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6389  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6394  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6399  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6404  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6409  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6414  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6419  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____6424  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____6429  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6436  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____6441  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6446  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6451  ->
    let uu____6452 = get_smtencoding_nl_arith_repr ()  in
    uu____6452 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6457  ->
    let uu____6458 = get_smtencoding_nl_arith_repr ()  in
    uu____6458 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6463  ->
    let uu____6464 = get_smtencoding_nl_arith_repr ()  in
    uu____6464 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6469  ->
    let uu____6470 = get_smtencoding_l_arith_repr ()  in
    uu____6470 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6475  ->
    let uu____6476 = get_smtencoding_l_arith_repr ()  in
    uu____6476 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6481  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6486  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6491  -> get_tactic_trace_d () 
let (timing : unit -> Prims.bool) = fun uu____6496  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____6501  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____6506  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____6511  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____6516  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____6521  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____6526  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6533  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____6538  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____6549  ->
    let uu____6550 = get_using_facts_from ()  in
    match uu____6550 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____6580  ->
    let uu____6581 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____6581
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____6588  ->
    let uu____6589 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____6589 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____6592 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____6599  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____6604  ->
    let uu____6605 = get_smt ()  in
    match uu____6605 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____6615  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____6620  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____6625  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____6630  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____6635  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____6640  ->
    (get_use_two_phase_tc ()) &&
      (let uu____6642 = lax ()  in Prims.op_Negation uu____6642)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____6647  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____6652  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____6657  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____6662  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____6669 = get_extract ()  in
    match uu____6669 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____6680 =
            let uu____6693 = get_no_extract ()  in
            let uu____6696 = get_extract_namespace ()  in
            let uu____6699 = get_extract_module ()  in
            (uu____6693, uu____6696, uu____6699)  in
          match uu____6680 with
          | ([],[],[]) -> ()
          | uu____6714 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = FStar_Ident.path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____6760,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____6779 -> false  in
          let uu____6788 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____6822  ->
                    match uu____6822 with
                    | (path,uu____6830) -> matches_path m_components path))
             in
          match uu____6788 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____6841,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____6861 = get_extract_namespace ()  in
          match uu____6861 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____6877 = get_extract_module ()  in
          match uu____6877 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____6889 = no_extract m1  in Prims.op_Negation uu____6889) &&
          (let uu____6891 =
             let uu____6900 = get_extract_namespace ()  in
             let uu____6903 = get_extract_module ()  in
             (uu____6900, uu____6903)  in
           (match uu____6891 with
            | ([],[]) -> true
            | uu____6914 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  