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
  fun uu____1186  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1203  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1268 =
      let uu____1271 = peek ()  in FStar_Util.smap_try_find uu____1271 s  in
    match uu____1268 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1281 . Prims.string -> (option_val -> 'Auu____1281) -> 'Auu____1281
  = fun s  -> fun c  -> let uu____1297 = get_option s  in c uu____1297 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1302  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1309  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1316  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1323  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1330  -> lookup_opt "cache_off" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1337  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1346  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1355  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1364  -> lookup_opt "debug_level" (as_list as_string) 
let (get_defensive : unit -> Prims.string) =
  fun uu____1371  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1378  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1385  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1390  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1395  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1402  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1409  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1414  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1423  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1436  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1445  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1452  -> lookup_opt "fs_typ_app" as_bool 
let (get_fstar_home : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1459  -> lookup_opt "fstar_home" (as_option as_string) 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1466  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1471  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1478  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1485  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1490  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1497  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1504  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1509  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1514  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1519  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1526  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1533  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1538  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1543  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1548  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1553  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1558  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1563  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1568  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1575  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1582  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1587  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1592  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1599  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1606  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1613  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1620  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1625  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1630  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1635  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1640  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1645  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1650  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1655  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1660  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1667  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1674  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1681  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1688  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1693  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1698  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1703  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1708  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1713  -> lookup_opt "tactic_trace_d" as_int 
let (get_timing : unit -> Prims.bool) =
  fun uu____1718  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1723  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1728  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1733  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1738  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1743  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1748  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1755  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1762  ->
    let uu____1763 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1763
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1772  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1785  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1794  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1803  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1810  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1815  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1822  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1829  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1834  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1839  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1844  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1849  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1854  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1859  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1864  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1869  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___70_1874  ->
    match uu___70_1874 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1886 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1892 = get_debug_level ()  in
    FStar_All.pipe_right uu____1892
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2025  ->
    let uu____2026 =
      let uu____2027 = FStar_ST.op_Bang _version  in
      let uu____2051 = FStar_ST.op_Bang _platform  in
      let uu____2075 = FStar_ST.op_Bang _compiler  in
      let uu____2099 = FStar_ST.op_Bang _date  in
      let uu____2123 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2027
        uu____2051 uu____2075 uu____2099 uu____2123
       in
    FStar_Util.print_string uu____2026
  
let display_usage_aux :
  'Auu____2153 'Auu____2154 .
    ('Auu____2153,Prims.string,'Auu____2154 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2202  ->
         match uu____2202 with
         | (uu____2213,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2225 =
                      let uu____2226 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2226  in
                    FStar_Util.print_string uu____2225
                  else
                    (let uu____2228 =
                       let uu____2229 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2229 doc  in
                     FStar_Util.print_string uu____2228)
              | FStar_Getopt.OneArg (uu____2230,argname) ->
                  if doc = ""
                  then
                    let uu____2238 =
                      let uu____2239 = FStar_Util.colorize_bold flag  in
                      let uu____2240 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2239 uu____2240
                       in
                    FStar_Util.print_string uu____2238
                  else
                    (let uu____2242 =
                       let uu____2243 = FStar_Util.colorize_bold flag  in
                       let uu____2244 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2243
                         uu____2244 doc
                        in
                     FStar_Util.print_string uu____2242))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2272 = o  in
    match uu____2272 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2308 =
                let uu____2309 = f ()  in set_option name uu____2309  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2324 = f x  in set_option name uu____2324
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2344 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2344  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2367 =
        let uu____2370 = lookup_opt name as_list'  in
        FStar_List.append uu____2370 [value]  in
      mk_list uu____2367
  
let accumulate_string :
  'Auu____2383 .
    Prims.string -> ('Auu____2383 -> Prims.string) -> 'Auu____2383 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2404 =
          let uu____2405 =
            let uu____2406 = post_processor value  in mk_string uu____2406
             in
          accumulated_option name uu____2405  in
        set_option name uu____2404
  
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
    match projectee with | Const _0 -> true | uu____2502 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2516 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2529 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2536 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2550 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2566 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2592 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2631 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2666 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2680 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2701 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2739 -> true
    | uu____2740 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2747 -> uu____2747
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2767 ->
              let uu____2768 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2768 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2772 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2772
          | PathStr uu____2775 -> mk_path str_val
          | SimpleStr uu____2776 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2781 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2796 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2796
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
            let uu____2815 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2815
  
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
    | PostProcessed (uu____2852,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2862,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2889 = desc_of_opt_type typ  in
      match uu____2889 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2895  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2912 =
      let uu____2913 = as_string s  in FStar_String.lowercase uu____2913  in
    mk_string uu____2912
  
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2935  ->
    let uu____2947 =
      let uu____2959 =
        let uu____2971 =
          let uu____2981 = let uu____2982 = mk_bool true  in Const uu____2982
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2981,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
           in
        let uu____2984 =
          let uu____2996 =
            let uu____3008 =
              let uu____3018 =
                let uu____3019 = mk_bool true  in Const uu____3019  in
              (FStar_Getopt.noshort, "cache_off", uu____3018,
                "Do not read or write any .checked files")
               in
            let uu____3021 =
              let uu____3033 =
                let uu____3045 =
                  let uu____3057 =
                    let uu____3069 =
                      let uu____3081 =
                        let uu____3093 =
                          let uu____3105 =
                            let uu____3115 =
                              let uu____3116 = mk_bool true  in
                              Const uu____3116  in
                            (FStar_Getopt.noshort, "detail_errors",
                              uu____3115,
                              "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                             in
                          let uu____3118 =
                            let uu____3130 =
                              let uu____3140 =
                                let uu____3141 = mk_bool true  in
                                Const uu____3141  in
                              (FStar_Getopt.noshort, "detail_hint_replay",
                                uu____3140,
                                "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                               in
                            let uu____3143 =
                              let uu____3155 =
                                let uu____3165 =
                                  let uu____3166 = mk_bool true  in
                                  Const uu____3166  in
                                (FStar_Getopt.noshort, "doc", uu____3165,
                                  "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                 in
                              let uu____3168 =
                                let uu____3180 =
                                  let uu____3192 =
                                    let uu____3202 =
                                      let uu____3203 = mk_bool true  in
                                      Const uu____3203  in
                                    (FStar_Getopt.noshort, "eager_inference",
                                      uu____3202,
                                      "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                     in
                                  let uu____3205 =
                                    let uu____3217 =
                                      let uu____3227 =
                                        let uu____3228 = mk_bool true  in
                                        Const uu____3228  in
                                      (FStar_Getopt.noshort,
                                        "eager_subtyping", uu____3227,
                                        "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                       in
                                    let uu____3230 =
                                      let uu____3242 =
                                        let uu____3254 =
                                          let uu____3266 =
                                            let uu____3278 =
                                              let uu____3288 =
                                                let uu____3289 = mk_bool true
                                                   in
                                                Const uu____3289  in
                                              (FStar_Getopt.noshort,
                                                "expose_interfaces",
                                                uu____3288,
                                                "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                               in
                                            let uu____3291 =
                                              let uu____3303 =
                                                let uu____3315 =
                                                  let uu____3325 =
                                                    let uu____3326 =
                                                      mk_bool true  in
                                                    Const uu____3326  in
                                                  (FStar_Getopt.noshort,
                                                    "hide_uvar_nums",
                                                    uu____3325,
                                                    "Don't print unification variable numbers")
                                                   in
                                                let uu____3328 =
                                                  let uu____3340 =
                                                    let uu____3352 =
                                                      let uu____3362 =
                                                        let uu____3363 =
                                                          mk_bool true  in
                                                        Const uu____3363  in
                                                      (FStar_Getopt.noshort,
                                                        "hint_info",
                                                        uu____3362,
                                                        "Print information regarding hints (deprecated; use --query_stats instead)")
                                                       in
                                                    let uu____3365 =
                                                      let uu____3377 =
                                                        let uu____3387 =
                                                          let uu____3388 =
                                                            mk_bool true  in
                                                          Const uu____3388
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "in", uu____3387,
                                                          "Legacy interactive mode; reads input from stdin")
                                                         in
                                                      let uu____3390 =
                                                        let uu____3402 =
                                                          let uu____3412 =
                                                            let uu____3413 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3413
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "ide",
                                                            uu____3412,
                                                            "JSON-based interactive mode for IDEs")
                                                           in
                                                        let uu____3415 =
                                                          let uu____3427 =
                                                            let uu____3439 =
                                                              let uu____3449
                                                                =
                                                                let uu____3450
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____3450
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "indent",
                                                                uu____3449,
                                                                "Parses and outputs the files on the command line")
                                                               in
                                                            let uu____3452 =
                                                              let uu____3464
                                                                =
                                                                let uu____3476
                                                                  =
                                                                  let uu____3488
                                                                    =
                                                                    let uu____3498
                                                                    =
                                                                    let uu____3499
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3499
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3498,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                  let uu____3501
                                                                    =
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
                                                                    "log_types",
                                                                    uu____3535,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3538
                                                                    =
                                                                    let uu____3550
                                                                    =
                                                                    let uu____3560
                                                                    =
                                                                    let uu____3561
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3561
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3560,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3563
                                                                    =
                                                                    let uu____3575
                                                                    =
                                                                    let uu____3587
                                                                    =
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
                                                                    "MLish",
                                                                    uu____3621,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3624
                                                                    =
                                                                    let uu____3636
                                                                    =
                                                                    let uu____3648
                                                                    =
                                                                    let uu____3658
                                                                    =
                                                                    let uu____3659
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3659
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3658,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3661
                                                                    =
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
                                                                    "no_location_info",
                                                                    uu____3695,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
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
                                                                    "no_smt",
                                                                    uu____3720,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3723
                                                                    =
                                                                    let uu____3735
                                                                    =
                                                                    let uu____3745
                                                                    =
                                                                    let uu____3746
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3746
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3745,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3748
                                                                    =
                                                                    let uu____3760
                                                                    =
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
                                                                    "print_bound_var_types",
                                                                    uu____3794,
                                                                    "Print the types of bound variables")
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
                                                                    "print_effect_args",
                                                                    uu____3819,
                                                                    "Print inferred predicate transformers for all computation types")
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
                                                                    "print_full_names",
                                                                    uu____3844,
                                                                    "Print full names of variables")
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
                                                                    "print_implicits",
                                                                    uu____3869,
                                                                    "Print implicit arguments")
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
                                                                    "print_universes",
                                                                    uu____3894,
                                                                    "Print universes")
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
                                                                    "print_z3_statistics",
                                                                    uu____3919,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
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
                                                                    "prn",
                                                                    uu____3944,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
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
                                                                    "query_stats",
                                                                    uu____3969,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3972
                                                                    =
                                                                    let uu____3984
                                                                    =
                                                                    let uu____3994
                                                                    =
                                                                    let uu____3995
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3995
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3994,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3997
                                                                    =
                                                                    let uu____4009
                                                                    =
                                                                    let uu____4021
                                                                    =
                                                                    let uu____4031
                                                                    =
                                                                    let uu____4032
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4032
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4031,
                                                                    " ")  in
                                                                    let uu____4034
                                                                    =
                                                                    let uu____4046
                                                                    =
                                                                    let uu____4058
                                                                    =
                                                                    let uu____4070
                                                                    =
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
                                                                    "tactic_raw_binders",
                                                                    uu____4104,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4107
                                                                    =
                                                                    let uu____4119
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
                                                                    "tactic_trace",
                                                                    uu____4129,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4132
                                                                    =
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
                                                                    "timing",
                                                                    uu____4166,
                                                                    "Print the time it takes to verify each top-level definition")
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
                                                                    "trace_error",
                                                                    uu____4191,
                                                                    "Don't print an error message; show an exception trace instead")
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
                                                                    "ugly",
                                                                    uu____4216,
                                                                    "Emit output formatted for debugging")
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
                                                                    "unthrottle_inductives",
                                                                    uu____4241,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
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
                                                                    "unsafe_tactic_exec",
                                                                    uu____4266,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
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
                                                                    "use_eq_at_higher_order",
                                                                    uu____4291,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
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
                                                                    "use_hints",
                                                                    uu____4316,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4319
                                                                    =
                                                                    let uu____4331
                                                                    =
                                                                    let uu____4341
                                                                    =
                                                                    let uu____4342
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4342
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4341,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4344
                                                                    =
                                                                    let uu____4356
                                                                    =
                                                                    let uu____4368
                                                                    =
                                                                    let uu____4378
                                                                    =
                                                                    let uu____4379
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4379
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4378,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4381
                                                                    =
                                                                    let uu____4393
                                                                    =
                                                                    let uu____4405
                                                                    =
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
                                                                    "__temp_fast_implicits",
                                                                    uu____4439,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4442
                                                                    =
                                                                    let uu____4454
                                                                    =
                                                                    let uu____4464
                                                                    =
                                                                    let uu____4465
                                                                    =
                                                                    let uu____4473
                                                                    =
                                                                    let uu____4474
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4474
                                                                     in
                                                                    ((fun
                                                                    uu____4480
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4473)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4465
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4464,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4484
                                                                    =
                                                                    let uu____4496
                                                                    =
                                                                    let uu____4506
                                                                    =
                                                                    let uu____4507
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4507
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4506,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4509
                                                                    =
                                                                    let uu____4521
                                                                    =
                                                                    let uu____4533
                                                                    =
                                                                    let uu____4543
                                                                    =
                                                                    let uu____4544
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4544
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4543,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4546
                                                                    =
                                                                    let uu____4558
                                                                    =
                                                                    let uu____4570
                                                                    =
                                                                    let uu____4582
                                                                    =
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
                                                                    "__no_positivity",
                                                                    uu____4616,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4619
                                                                    =
                                                                    let uu____4631
                                                                    =
                                                                    let uu____4641
                                                                    =
                                                                    let uu____4642
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4642
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4641,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4644
                                                                    =
                                                                    let uu____4656
                                                                    =
                                                                    let uu____4668
                                                                    =
                                                                    let uu____4680
                                                                    =
                                                                    let uu____4690
                                                                    =
                                                                    let uu____4691
                                                                    =
                                                                    let uu____4699
                                                                    =
                                                                    let uu____4700
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4700
                                                                     in
                                                                    ((fun
                                                                    uu____4706
                                                                     ->
                                                                    (
                                                                    let uu____4708
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4708);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4699)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4691
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4690,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4680]
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4668
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4656
                                                                     in
                                                                    uu____4631
                                                                    ::
                                                                    uu____4644
                                                                     in
                                                                    uu____4606
                                                                    ::
                                                                    uu____4619
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4594
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4582
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4570
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4558
                                                                     in
                                                                    uu____4533
                                                                    ::
                                                                    uu____4546
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4521
                                                                     in
                                                                    uu____4496
                                                                    ::
                                                                    uu____4509
                                                                     in
                                                                    uu____4454
                                                                    ::
                                                                    uu____4484
                                                                     in
                                                                    uu____4429
                                                                    ::
                                                                    uu____4442
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4417
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4405
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4393
                                                                     in
                                                                    uu____4368
                                                                    ::
                                                                    uu____4381
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4356
                                                                     in
                                                                    uu____4331
                                                                    ::
                                                                    uu____4344
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
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4144
                                                                     in
                                                                    uu____4119
                                                                    ::
                                                                    uu____4132
                                                                     in
                                                                    uu____4094
                                                                    ::
                                                                    uu____4107
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4082
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4070
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4058
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4046
                                                                     in
                                                                    uu____4021
                                                                    ::
                                                                    uu____4034
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____4009
                                                                     in
                                                                    uu____3984
                                                                    ::
                                                                    uu____3997
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
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3772
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3760
                                                                     in
                                                                    uu____3735
                                                                    ::
                                                                    uu____3748
                                                                     in
                                                                    uu____3710
                                                                    ::
                                                                    uu____3723
                                                                     in
                                                                    uu____3685
                                                                    ::
                                                                    uu____3698
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3673
                                                                     in
                                                                    uu____3648
                                                                    ::
                                                                    uu____3661
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3636
                                                                     in
                                                                    uu____3611
                                                                    ::
                                                                    uu____3624
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3599
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3587
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3575
                                                                     in
                                                                    uu____3550
                                                                    ::
                                                                    uu____3563
                                                                     in
                                                                    uu____3525
                                                                    ::
                                                                    uu____3538
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3513
                                                                     in
                                                                  uu____3488
                                                                    ::
                                                                    uu____3501
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_ifuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                  ::
                                                                  uu____3476
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_fuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of recursive functions to try initially (default 2)")
                                                                :: uu____3464
                                                               in
                                                            uu____3439 ::
                                                              uu____3452
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "include",
                                                            (ReverseAccumulated
                                                               (PathStr
                                                                  "path")),
                                                            "A directory in which to search for files included on the command line")
                                                            :: uu____3427
                                                           in
                                                        uu____3402 ::
                                                          uu____3415
                                                         in
                                                      uu____3377 ::
                                                        uu____3390
                                                       in
                                                    uu____3352 :: uu____3365
                                                     in
                                                  (FStar_Getopt.noshort,
                                                    "hint_file",
                                                    (PathStr "path"),
                                                    "Read/write hints to <path> (instead of module-specific hints files)")
                                                    :: uu____3340
                                                   in
                                                uu____3315 :: uu____3328  in
                                              (FStar_Getopt.noshort,
                                                "fstar_home",
                                                (PathStr "dir"),
                                                "Set the FSTAR_HOME variable to <dir>")
                                                :: uu____3303
                                               in
                                            uu____3278 :: uu____3291  in
                                          (FStar_Getopt.noshort,
                                            "extract_namespace",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr
                                                       "namespace name")))),
                                            "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                            :: uu____3266
                                           in
                                        (FStar_Getopt.noshort,
                                          "extract_module",
                                          (Accumulated
                                             (PostProcessed
                                                (pp_lowercase,
                                                  (SimpleStr "module_name")))),
                                          "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                          :: uu____3254
                                         in
                                      (FStar_Getopt.noshort, "extract",
                                        (Accumulated
                                           (SimpleStr
                                              "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                        "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                        :: uu____3242
                                       in
                                    uu____3217 :: uu____3230  in
                                  uu____3192 :: uu____3205  in
                                (FStar_Getopt.noshort, "dump_module",
                                  (Accumulated (SimpleStr "module_name")),
                                  "") :: uu____3180
                                 in
                              uu____3155 :: uu____3168  in
                            uu____3130 :: uu____3143  in
                          uu____3105 :: uu____3118  in
                        (FStar_Getopt.noshort, "dep",
                          (EnumStr ["make"; "graph"; "full"]),
                          "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                          :: uu____3093
                         in
                      (FStar_Getopt.noshort, "defensive",
                        (EnumStr ["no"; "warn"; "fail"]),
                        "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                        :: uu____3081
                       in
                    (FStar_Getopt.noshort, "debug_level",
                      (Accumulated
                         (OpenEnumStr
                            (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                      "Control the verbosity of debugging info") ::
                      uu____3069
                     in
                  (FStar_Getopt.noshort, "debug",
                    (Accumulated (SimpleStr "module_name")),
                    "Print lots of debugging information while checking module")
                    :: uu____3057
                   in
                (FStar_Getopt.noshort, "codegen-lib",
                  (Accumulated (SimpleStr "namespace")),
                  "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                  :: uu____3045
                 in
              (FStar_Getopt.noshort, "codegen",
                (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                "Generate code for further compilation to executable code, or build a compiler plugin")
                :: uu____3033
               in
            uu____3008 :: uu____3021  in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2996
           in
        uu____2971 :: uu____2984  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2959
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2947

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5619  ->
    let uu____5622 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5649  ->
         match uu____5649 with
         | (short,long,typ,doc) ->
             let uu____5665 =
               let uu____5677 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5677, doc)  in
             mk_spec uu____5665) uu____5622

let (settable : Prims.string -> Prims.bool) =
  fun uu___71_5687  ->
    match uu___71_5687 with
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
    | uu____5688 -> false
  
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
       (fun uu____5762  ->
          match uu____5762 with
          | (uu____5774,x,uu____5776,uu____5777) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5839  ->
          match uu____5839 with
          | (uu____5851,x,uu____5853,uu____5854) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5865  ->
    let uu____5866 = specs ()  in display_usage_aux uu____5866
  
let (fstar_home : unit -> Prims.string) =
  fun uu____5885  ->
    let uu____5886 = get_fstar_home ()  in
    match uu____5886 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir ()  in
        let x1 = Prims.strcat x "/.."  in
        ((let uu____5892 =
            let uu____5897 = mk_string x1  in ("fstar_home", uu____5897)  in
          set_option' uu____5892);
         x1)
    | FStar_Pervasives_Native.Some x -> x
  
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5908 -> true
    | uu____5909 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5916 -> uu____5916
  
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
          let uu____5944 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5944
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5972  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5977 =
             let uu____5980 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5980 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5977)
       in
    let uu____6037 =
      let uu____6040 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6040
       in
    (res, uu____6037)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6078  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6117 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6117 (fun x  -> ())  in
     (let uu____6123 =
        let uu____6128 =
          let uu____6129 = FStar_List.map mk_string old_verify_module  in
          List uu____6129  in
        ("verify_module", uu____6128)  in
      set_option' uu____6123);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6139 =
        let uu____6140 =
          let uu____6141 =
            let uu____6142 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6142  in
          (FStar_String.length f1) - uu____6141  in
        uu____6140 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6139  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6148 = get_lax ()  in
    if uu____6148
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6158 = module_name_of_file_name fn  in should_verify uu____6158
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6164 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6164
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6172 = should_verify m  in
    if uu____6172 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6180  ->
    let uu____6181 = get_no_default_includes ()  in
    if uu____6181
    then get_include ()
    else
      (let h = fstar_home ()  in
       let defs = universe_include_path_base_dirs  in
       let uu____6189 =
         let uu____6192 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x))
            in
         FStar_All.pipe_right uu____6192
           (FStar_List.filter FStar_Util.file_exists)
          in
       let uu____6205 =
         let uu____6208 = get_include ()  in
         FStar_List.append uu____6208 ["."]  in
       FStar_List.append uu____6189 uu____6205)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun filename  ->
    let uu____6218 = FStar_Util.is_path_absolute filename  in
    if uu____6218
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____6225 =
         let uu____6228 = include_path ()  in FStar_List.rev uu____6228  in
       FStar_Util.find_map uu____6225
         (fun p  ->
            let path =
              if p = "." then filename else FStar_Util.join_paths p filename
               in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
  
let (prims : unit -> Prims.string) =
  fun uu____6243  ->
    let uu____6244 = get_prims ()  in
    match uu____6244 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6248 = find_file filename  in
        (match uu____6248 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6252 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6252)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6258  ->
    let uu____6259 = prims ()  in FStar_Util.basename uu____6259
  
let (pervasives : unit -> Prims.string) =
  fun uu____6264  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____6266 = find_file filename  in
    match uu____6266 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____6270 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6270
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6275  ->
    let uu____6276 = pervasives ()  in FStar_Util.basename uu____6276
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6281  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____6283 = find_file filename  in
    match uu____6283 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____6287 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6287
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____6293 = get_odir ()  in
    match uu____6293 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____6302 = get_cache_dir ()  in
    match uu____6302 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6306 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____6306
  
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
             let uu____6354 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             FStar_Ident.path_of_text uu____6354  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           let uu____6358 = FStar_Ident.path_of_text s1  in
           (uu____6358, true))
       in
    let uu____6359 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6359 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6423 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6423 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6432  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6437  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6444  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6449  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____6454  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6460 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6466 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6472 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6478 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6485  ->
    let uu____6486 = get_codegen ()  in
    FStar_Util.map_opt uu____6486
      (fun uu___72_6490  ->
         match uu___72_6490 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6491 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6500  ->
    let uu____6501 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6501
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6518  -> let uu____6519 = get_debug ()  in uu____6519 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6529 = get_debug ()  in
    FStar_All.pipe_right uu____6529 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6546 = get_debug ()  in
       FStar_All.pipe_right uu____6546 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6555  -> let uu____6556 = get_defensive ()  in uu____6556 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6561  ->
    let uu____6562 = get_defensive ()  in uu____6562 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6569  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6574  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6579  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6584  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6590 = get_dump_module ()  in
    FStar_All.pipe_right uu____6590 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6599  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6604  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6610 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6610
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6644  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6649  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6654  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6661  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6666  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6671  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6676  ->
    let uu____6677 = get_initial_fuel ()  in
    let uu____6678 = get_max_fuel ()  in Prims.min uu____6677 uu____6678
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6683  ->
    let uu____6684 = get_initial_ifuel ()  in
    let uu____6685 = get_max_ifuel ()  in Prims.min uu____6684 uu____6685
  
let (interactive : unit -> Prims.bool) =
  fun uu____6690  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6695  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6702  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6707  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6712  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6717  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6722  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6727  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6732  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6737  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6742  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6747  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6752  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6759 = get_no_extract ()  in
    FStar_All.pipe_right uu____6759
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6770  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6775  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6780  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6787  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6792  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6797  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6802  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6807  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6812  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6817  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6822  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____6827  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____6832  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6839  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____6844  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6849  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6854  ->
    let uu____6855 = get_smtencoding_nl_arith_repr ()  in
    uu____6855 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6860  ->
    let uu____6861 = get_smtencoding_nl_arith_repr ()  in
    uu____6861 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6866  ->
    let uu____6867 = get_smtencoding_nl_arith_repr ()  in
    uu____6867 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6872  ->
    let uu____6873 = get_smtencoding_l_arith_repr ()  in
    uu____6873 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6878  ->
    let uu____6879 = get_smtencoding_l_arith_repr ()  in
    uu____6879 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6884  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6889  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6894  -> get_tactic_trace_d () 
let (timing : unit -> Prims.bool) = fun uu____6899  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____6904  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____6909  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____6914  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____6919  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____6924  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____6929  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6936  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____6941  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____6952  ->
    let uu____6953 = get_using_facts_from ()  in
    match uu____6953 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____6983  ->
    let uu____6984 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____6984
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____6991  ->
    let uu____6992 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____6992 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____6995 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7002  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____7007  ->
    let uu____7008 = get_smt ()  in
    match uu____7008 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7018  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____7023  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____7028  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7033  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____7038  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7043  ->
    (get_use_two_phase_tc ()) &&
      (let uu____7045 = lax ()  in Prims.op_Negation uu____7045)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7050  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7055  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7060  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7065  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7072 = get_extract ()  in
    match uu____7072 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7083 =
            let uu____7096 = get_no_extract ()  in
            let uu____7099 = get_extract_namespace ()  in
            let uu____7102 = get_extract_module ()  in
            (uu____7096, uu____7099, uu____7102)  in
          match uu____7083 with
          | ([],[],[]) -> ()
          | uu____7117 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = FStar_Ident.path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7163,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7182 -> false  in
          let uu____7191 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7225  ->
                    match uu____7225 with
                    | (path,uu____7233) -> matches_path m_components path))
             in
          match uu____7191 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____7244,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____7264 = get_extract_namespace ()  in
          match uu____7264 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____7280 = get_extract_module ()  in
          match uu____7280 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____7292 = no_extract m1  in Prims.op_Negation uu____7292) &&
          (let uu____7294 =
             let uu____7303 = get_extract_namespace ()  in
             let uu____7306 = get_extract_module ()  in
             (uu____7303, uu____7306)  in
           (match uu____7294 with
            | ([],[]) -> true
            | uu____7317 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  