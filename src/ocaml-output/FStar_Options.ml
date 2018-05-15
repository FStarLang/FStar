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
    let uu____2270 = o  in
    match uu____2270 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2303 =
                let uu____2304 = f ()  in set_option name uu____2304  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2319 = f x  in set_option name uu____2319
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2338 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2338  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2361 =
        let uu____2364 = lookup_opt name as_list'  in
        FStar_List.append uu____2364 [value]  in
      mk_list uu____2361
  
let accumulate_string :
  'Auu____2377 .
    Prims.string -> ('Auu____2377 -> Prims.string) -> 'Auu____2377 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2398 =
          let uu____2399 =
            let uu____2400 = post_processor value  in mk_string uu____2400
             in
          accumulated_option name uu____2399  in
        set_option name uu____2398
  
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
    match projectee with | Const _0 -> true | uu____2496 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2510 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2523 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2530 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2544 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2560 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2586 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2625 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2660 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2674 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2695 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2733 -> true
    | uu____2734 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2741 -> uu____2741
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2761 ->
              let uu____2762 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2762 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2766 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2766
          | PathStr uu____2769 -> mk_path str_val
          | SimpleStr uu____2770 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2775 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2790 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2790
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
            let uu____2809 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2809
  
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
    | PostProcessed (uu____2846,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2856,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2883 = desc_of_opt_type typ  in
      match uu____2883 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2889  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2906 =
      let uu____2907 = as_string s  in FStar_String.lowercase uu____2907  in
    mk_string uu____2906
  
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2928  ->
    let uu____2939 =
      let uu____2950 =
        let uu____2961 =
          let uu____2970 = let uu____2971 = mk_bool true  in Const uu____2971
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2970,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
           in
        let uu____2972 =
          let uu____2983 =
            let uu____2994 =
              let uu____3003 =
                let uu____3004 = mk_bool true  in Const uu____3004  in
              (FStar_Getopt.noshort, "cache_off", uu____3003,
                "Do not read or write any .checked files")
               in
            let uu____3005 =
              let uu____3016 =
                let uu____3027 =
                  let uu____3038 =
                    let uu____3049 =
                      let uu____3060 =
                        let uu____3071 =
                          let uu____3082 =
                            let uu____3091 =
                              let uu____3092 = mk_bool true  in
                              Const uu____3092  in
                            (FStar_Getopt.noshort, "detail_errors",
                              uu____3091,
                              "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                             in
                          let uu____3093 =
                            let uu____3104 =
                              let uu____3113 =
                                let uu____3114 = mk_bool true  in
                                Const uu____3114  in
                              (FStar_Getopt.noshort, "detail_hint_replay",
                                uu____3113,
                                "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                               in
                            let uu____3115 =
                              let uu____3126 =
                                let uu____3135 =
                                  let uu____3136 = mk_bool true  in
                                  Const uu____3136  in
                                (FStar_Getopt.noshort, "doc", uu____3135,
                                  "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                 in
                              let uu____3137 =
                                let uu____3148 =
                                  let uu____3159 =
                                    let uu____3168 =
                                      let uu____3169 = mk_bool true  in
                                      Const uu____3169  in
                                    (FStar_Getopt.noshort, "eager_inference",
                                      uu____3168,
                                      "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                     in
                                  let uu____3170 =
                                    let uu____3181 =
                                      let uu____3190 =
                                        let uu____3191 = mk_bool true  in
                                        Const uu____3191  in
                                      (FStar_Getopt.noshort,
                                        "eager_subtyping", uu____3190,
                                        "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                       in
                                    let uu____3192 =
                                      let uu____3203 =
                                        let uu____3214 =
                                          let uu____3225 =
                                            let uu____3236 =
                                              let uu____3245 =
                                                let uu____3246 = mk_bool true
                                                   in
                                                Const uu____3246  in
                                              (FStar_Getopt.noshort,
                                                "expose_interfaces",
                                                uu____3245,
                                                "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                               in
                                            let uu____3247 =
                                              let uu____3258 =
                                                let uu____3269 =
                                                  let uu____3278 =
                                                    let uu____3279 =
                                                      mk_bool true  in
                                                    Const uu____3279  in
                                                  (FStar_Getopt.noshort,
                                                    "hide_uvar_nums",
                                                    uu____3278,
                                                    "Don't print unification variable numbers")
                                                   in
                                                let uu____3280 =
                                                  let uu____3291 =
                                                    let uu____3302 =
                                                      let uu____3311 =
                                                        let uu____3312 =
                                                          mk_bool true  in
                                                        Const uu____3312  in
                                                      (FStar_Getopt.noshort,
                                                        "hint_info",
                                                        uu____3311,
                                                        "Print information regarding hints (deprecated; use --query_stats instead)")
                                                       in
                                                    let uu____3313 =
                                                      let uu____3324 =
                                                        let uu____3333 =
                                                          let uu____3334 =
                                                            mk_bool true  in
                                                          Const uu____3334
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "in", uu____3333,
                                                          "Legacy interactive mode; reads input from stdin")
                                                         in
                                                      let uu____3335 =
                                                        let uu____3346 =
                                                          let uu____3355 =
                                                            let uu____3356 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3356
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "ide",
                                                            uu____3355,
                                                            "JSON-based interactive mode for IDEs")
                                                           in
                                                        let uu____3357 =
                                                          let uu____3368 =
                                                            let uu____3379 =
                                                              let uu____3388
                                                                =
                                                                let uu____3389
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____3389
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "indent",
                                                                uu____3388,
                                                                "Parses and outputs the files on the command line")
                                                               in
                                                            let uu____3390 =
                                                              let uu____3401
                                                                =
                                                                let uu____3412
                                                                  =
                                                                  let uu____3423
                                                                    =
                                                                    let uu____3432
                                                                    =
                                                                    let uu____3433
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3433
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3432,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                  let uu____3434
                                                                    =
                                                                    let uu____3445
                                                                    =
                                                                    let uu____3456
                                                                    =
                                                                    let uu____3465
                                                                    =
                                                                    let uu____3466
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3466
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3465,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3467
                                                                    =
                                                                    let uu____3478
                                                                    =
                                                                    let uu____3487
                                                                    =
                                                                    let uu____3488
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3488
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3487,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3489
                                                                    =
                                                                    let uu____3500
                                                                    =
                                                                    let uu____3511
                                                                    =
                                                                    let uu____3522
                                                                    =
                                                                    let uu____3533
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
                                                                    "MLish",
                                                                    uu____3542,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3544
                                                                    =
                                                                    let uu____3555
                                                                    =
                                                                    let uu____3566
                                                                    =
                                                                    let uu____3575
                                                                    =
                                                                    let uu____3576
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3576
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3575,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3577
                                                                    =
                                                                    let uu____3588
                                                                    =
                                                                    let uu____3599
                                                                    =
                                                                    let uu____3608
                                                                    =
                                                                    let uu____3609
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3609
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3608,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3610
                                                                    =
                                                                    let uu____3621
                                                                    =
                                                                    let uu____3630
                                                                    =
                                                                    let uu____3631
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3631
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3630,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3632
                                                                    =
                                                                    let uu____3643
                                                                    =
                                                                    let uu____3652
                                                                    =
                                                                    let uu____3653
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3653
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3652,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3654
                                                                    =
                                                                    let uu____3665
                                                                    =
                                                                    let uu____3676
                                                                    =
                                                                    let uu____3687
                                                                    =
                                                                    let uu____3696
                                                                    =
                                                                    let uu____3697
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3697
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3696,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3698
                                                                    =
                                                                    let uu____3709
                                                                    =
                                                                    let uu____3718
                                                                    =
                                                                    let uu____3719
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3719
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3718,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3720
                                                                    =
                                                                    let uu____3731
                                                                    =
                                                                    let uu____3740
                                                                    =
                                                                    let uu____3741
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3741
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3740,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3742
                                                                    =
                                                                    let uu____3753
                                                                    =
                                                                    let uu____3762
                                                                    =
                                                                    let uu____3763
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3763
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3762,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3764
                                                                    =
                                                                    let uu____3775
                                                                    =
                                                                    let uu____3784
                                                                    =
                                                                    let uu____3785
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3785
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3784,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3786
                                                                    =
                                                                    let uu____3797
                                                                    =
                                                                    let uu____3806
                                                                    =
                                                                    let uu____3807
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3807
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3806,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3808
                                                                    =
                                                                    let uu____3819
                                                                    =
                                                                    let uu____3828
                                                                    =
                                                                    let uu____3829
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3829
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3828,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3830
                                                                    =
                                                                    let uu____3841
                                                                    =
                                                                    let uu____3850
                                                                    =
                                                                    let uu____3851
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3851
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3850,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3852
                                                                    =
                                                                    let uu____3863
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
                                                                    "record_hints",
                                                                    uu____3872,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3874
                                                                    =
                                                                    let uu____3885
                                                                    =
                                                                    let uu____3896
                                                                    =
                                                                    let uu____3905
                                                                    =
                                                                    let uu____3906
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3906
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3905,
                                                                    " ")  in
                                                                    let uu____3907
                                                                    =
                                                                    let uu____3918
                                                                    =
                                                                    let uu____3929
                                                                    =
                                                                    let uu____3940
                                                                    =
                                                                    let uu____3951
                                                                    =
                                                                    let uu____3962
                                                                    =
                                                                    let uu____3971
                                                                    =
                                                                    let uu____3972
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3972
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____3971,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____3973
                                                                    =
                                                                    let uu____3984
                                                                    =
                                                                    let uu____3993
                                                                    =
                                                                    let uu____3994
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3994
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____3993,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____3995
                                                                    =
                                                                    let uu____4006
                                                                    =
                                                                    let uu____4017
                                                                    =
                                                                    let uu____4026
                                                                    =
                                                                    let uu____4027
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4027
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4026,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4028
                                                                    =
                                                                    let uu____4039
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
                                                                    "trace_error",
                                                                    uu____4048,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4050
                                                                    =
                                                                    let uu____4061
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
                                                                    "ugly",
                                                                    uu____4070,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4072
                                                                    =
                                                                    let uu____4083
                                                                    =
                                                                    let uu____4092
                                                                    =
                                                                    let uu____4093
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4093
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4092,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4094
                                                                    =
                                                                    let uu____4105
                                                                    =
                                                                    let uu____4114
                                                                    =
                                                                    let uu____4115
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4115
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4114,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4116
                                                                    =
                                                                    let uu____4127
                                                                    =
                                                                    let uu____4136
                                                                    =
                                                                    let uu____4137
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4137
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4136,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4138
                                                                    =
                                                                    let uu____4149
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
                                                                    "use_hints",
                                                                    uu____4158,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4160
                                                                    =
                                                                    let uu____4171
                                                                    =
                                                                    let uu____4180
                                                                    =
                                                                    let uu____4181
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4181
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4180,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4182
                                                                    =
                                                                    let uu____4193
                                                                    =
                                                                    let uu____4204
                                                                    =
                                                                    let uu____4213
                                                                    =
                                                                    let uu____4214
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4214
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4213,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4215
                                                                    =
                                                                    let uu____4226
                                                                    =
                                                                    let uu____4237
                                                                    =
                                                                    let uu____4248
                                                                    =
                                                                    let uu____4259
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
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4268,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4270
                                                                    =
                                                                    let uu____4281
                                                                    =
                                                                    let uu____4290
                                                                    =
                                                                    let uu____4291
                                                                    =
                                                                    let uu____4299
                                                                    =
                                                                    let uu____4300
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4300
                                                                     in
                                                                    ((fun
                                                                    uu____4306
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4299)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4291
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4290,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4309
                                                                    =
                                                                    let uu____4320
                                                                    =
                                                                    let uu____4329
                                                                    =
                                                                    let uu____4330
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4330
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4329,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4331
                                                                    =
                                                                    let uu____4342
                                                                    =
                                                                    let uu____4353
                                                                    =
                                                                    let uu____4362
                                                                    =
                                                                    let uu____4363
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4363
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4362,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4364
                                                                    =
                                                                    let uu____4375
                                                                    =
                                                                    let uu____4386
                                                                    =
                                                                    let uu____4397
                                                                    =
                                                                    let uu____4408
                                                                    =
                                                                    let uu____4419
                                                                    =
                                                                    let uu____4428
                                                                    =
                                                                    let uu____4429
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4429
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4428,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4430
                                                                    =
                                                                    let uu____4441
                                                                    =
                                                                    let uu____4450
                                                                    =
                                                                    let uu____4451
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4451
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4450,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4452
                                                                    =
                                                                    let uu____4463
                                                                    =
                                                                    let uu____4474
                                                                    =
                                                                    let uu____4485
                                                                    =
                                                                    let uu____4494
                                                                    =
                                                                    let uu____4495
                                                                    =
                                                                    let uu____4503
                                                                    =
                                                                    let uu____4504
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4504
                                                                     in
                                                                    ((fun
                                                                    uu____4510
                                                                     ->
                                                                    (
                                                                    let uu____4512
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4512);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4503)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4495
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4494,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4485]
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4474
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4463
                                                                     in
                                                                    uu____4441
                                                                    ::
                                                                    uu____4452
                                                                     in
                                                                    uu____4419
                                                                    ::
                                                                    uu____4430
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4408
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4397
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4386
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4375
                                                                     in
                                                                    uu____4353
                                                                    ::
                                                                    uu____4364
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4342
                                                                     in
                                                                    uu____4320
                                                                    ::
                                                                    uu____4331
                                                                     in
                                                                    uu____4281
                                                                    ::
                                                                    uu____4309
                                                                     in
                                                                    uu____4259
                                                                    ::
                                                                    uu____4270
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4248
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4237
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4226
                                                                     in
                                                                    uu____4204
                                                                    ::
                                                                    uu____4215
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4193
                                                                     in
                                                                    uu____4171
                                                                    ::
                                                                    uu____4182
                                                                     in
                                                                    uu____4149
                                                                    ::
                                                                    uu____4160
                                                                     in
                                                                    uu____4127
                                                                    ::
                                                                    uu____4138
                                                                     in
                                                                    uu____4105
                                                                    ::
                                                                    uu____4116
                                                                     in
                                                                    uu____4083
                                                                    ::
                                                                    uu____4094
                                                                     in
                                                                    uu____4061
                                                                    ::
                                                                    uu____4072
                                                                     in
                                                                    uu____4039
                                                                    ::
                                                                    uu____4050
                                                                     in
                                                                    uu____4017
                                                                    ::
                                                                    uu____4028
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4006
                                                                     in
                                                                    uu____3984
                                                                    ::
                                                                    uu____3995
                                                                     in
                                                                    uu____3962
                                                                    ::
                                                                    uu____3973
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3951
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3940
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3929
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3918
                                                                     in
                                                                    uu____3896
                                                                    ::
                                                                    uu____3907
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3885
                                                                     in
                                                                    uu____3863
                                                                    ::
                                                                    uu____3874
                                                                     in
                                                                    uu____3841
                                                                    ::
                                                                    uu____3852
                                                                     in
                                                                    uu____3819
                                                                    ::
                                                                    uu____3830
                                                                     in
                                                                    uu____3797
                                                                    ::
                                                                    uu____3808
                                                                     in
                                                                    uu____3775
                                                                    ::
                                                                    uu____3786
                                                                     in
                                                                    uu____3753
                                                                    ::
                                                                    uu____3764
                                                                     in
                                                                    uu____3731
                                                                    ::
                                                                    uu____3742
                                                                     in
                                                                    uu____3709
                                                                    ::
                                                                    uu____3720
                                                                     in
                                                                    uu____3687
                                                                    ::
                                                                    uu____3698
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3676
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3665
                                                                     in
                                                                    uu____3643
                                                                    ::
                                                                    uu____3654
                                                                     in
                                                                    uu____3621
                                                                    ::
                                                                    uu____3632
                                                                     in
                                                                    uu____3599
                                                                    ::
                                                                    uu____3610
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3588
                                                                     in
                                                                    uu____3566
                                                                    ::
                                                                    uu____3577
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3555
                                                                     in
                                                                    uu____3533
                                                                    ::
                                                                    uu____3544
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3522
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3511
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3500
                                                                     in
                                                                    uu____3478
                                                                    ::
                                                                    uu____3489
                                                                     in
                                                                    uu____3456
                                                                    ::
                                                                    uu____3467
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3445
                                                                     in
                                                                  uu____3423
                                                                    ::
                                                                    uu____3434
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_ifuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                  ::
                                                                  uu____3412
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_fuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of recursive functions to try initially (default 2)")
                                                                :: uu____3401
                                                               in
                                                            uu____3379 ::
                                                              uu____3390
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "include",
                                                            (ReverseAccumulated
                                                               (PathStr
                                                                  "path")),
                                                            "A directory in which to search for files included on the command line")
                                                            :: uu____3368
                                                           in
                                                        uu____3346 ::
                                                          uu____3357
                                                         in
                                                      uu____3324 ::
                                                        uu____3335
                                                       in
                                                    uu____3302 :: uu____3313
                                                     in
                                                  (FStar_Getopt.noshort,
                                                    "hint_file",
                                                    (PathStr "path"),
                                                    "Read/write hints to <path> (instead of module-specific hints files)")
                                                    :: uu____3291
                                                   in
                                                uu____3269 :: uu____3280  in
                                              (FStar_Getopt.noshort,
                                                "fstar_home",
                                                (PathStr "dir"),
                                                "Set the FSTAR_HOME variable to <dir>")
                                                :: uu____3258
                                               in
                                            uu____3236 :: uu____3247  in
                                          (FStar_Getopt.noshort,
                                            "extract_namespace",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr
                                                       "namespace name")))),
                                            "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                            :: uu____3225
                                           in
                                        (FStar_Getopt.noshort,
                                          "extract_module",
                                          (Accumulated
                                             (PostProcessed
                                                (pp_lowercase,
                                                  (SimpleStr "module_name")))),
                                          "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                          :: uu____3214
                                         in
                                      (FStar_Getopt.noshort, "extract",
                                        (Accumulated
                                           (SimpleStr
                                              "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                        "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                        :: uu____3203
                                       in
                                    uu____3181 :: uu____3192  in
                                  uu____3159 :: uu____3170  in
                                (FStar_Getopt.noshort, "dump_module",
                                  (Accumulated (SimpleStr "module_name")),
                                  "") :: uu____3148
                                 in
                              uu____3126 :: uu____3137  in
                            uu____3104 :: uu____3115  in
                          uu____3082 :: uu____3093  in
                        (FStar_Getopt.noshort, "dep",
                          (EnumStr ["make"; "graph"; "full"]),
                          "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                          :: uu____3071
                         in
                      (FStar_Getopt.noshort, "defensive",
                        (EnumStr ["no"; "warn"; "fail"]),
                        "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                        :: uu____3060
                       in
                    (FStar_Getopt.noshort, "debug_level",
                      (Accumulated
                         (OpenEnumStr
                            (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                      "Control the verbosity of debugging info") ::
                      uu____3049
                     in
                  (FStar_Getopt.noshort, "debug",
                    (Accumulated (SimpleStr "module_name")),
                    "Print lots of debugging information while checking module")
                    :: uu____3038
                   in
                (FStar_Getopt.noshort, "codegen-lib",
                  (Accumulated (SimpleStr "namespace")),
                  "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                  :: uu____3027
                 in
              (FStar_Getopt.noshort, "codegen",
                (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                "Generate code for further compilation to executable code, or build a compiler plugin")
                :: uu____3016
               in
            uu____2994 :: uu____3005  in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2983
           in
        uu____2961 :: uu____2972  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2950
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2939

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5284  ->
    let uu____5287 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5312  ->
         match uu____5312 with
         | (short,long,typ,doc) ->
             let uu____5325 =
               let uu____5336 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5336, doc)  in
             mk_spec uu____5325) uu____5287

let (settable : Prims.string -> Prims.bool) =
  fun uu___71_5345  ->
    match uu___71_5345 with
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
    | uu____5346 -> false
  
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
       (fun uu____5415  ->
          match uu____5415 with
          | (uu____5426,x,uu____5428,uu____5429) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5485  ->
          match uu____5485 with
          | (uu____5496,x,uu____5498,uu____5499) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5508  ->
    let uu____5509 = specs ()  in display_usage_aux uu____5509
  
let (fstar_home : unit -> Prims.string) =
  fun uu____5526  ->
    let uu____5527 = get_fstar_home ()  in
    match uu____5527 with
    | FStar_Pervasives_Native.None  ->
        let x = FStar_Util.get_exec_dir ()  in
        let x1 = Prims.strcat x "/.."  in
        ((let uu____5533 =
            let uu____5538 = mk_string x1  in ("fstar_home", uu____5538)  in
          set_option' uu____5533);
         x1)
    | FStar_Pervasives_Native.Some x -> x
  
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5549 -> true
    | uu____5550 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5557 -> uu____5557
  
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
          let uu____5585 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5585
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5613  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5618 =
             let uu____5621 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5621 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5618)
       in
    let uu____5678 =
      let uu____5681 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5681
       in
    (res, uu____5678)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____5719  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____5758 = specs ()  in
       FStar_Getopt.parse_cmdline uu____5758 (fun x  -> ())  in
     (let uu____5764 =
        let uu____5769 =
          let uu____5770 = FStar_List.map mk_string old_verify_module  in
          List uu____5770  in
        ("verify_module", uu____5769)  in
      set_option' uu____5764);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____5780 =
        let uu____5781 =
          let uu____5782 =
            let uu____5783 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____5783  in
          (FStar_String.length f1) - uu____5782  in
        uu____5781 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5780  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5789 = get_lax ()  in
    if uu____5789
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____5799 = module_name_of_file_name fn  in should_verify uu____5799
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5805 = get___temp_no_proj ()  in
    FStar_List.contains m uu____5805
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____5813 = should_verify m  in
    if uu____5813 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____5821  ->
    let uu____5822 = get_no_default_includes ()  in
    if uu____5822
    then get_include ()
    else
      (let h = fstar_home ()  in
       let defs = universe_include_path_base_dirs  in
       let uu____5830 =
         let uu____5833 =
           FStar_All.pipe_right defs
             (FStar_List.map (fun x  -> Prims.strcat h x))
            in
         FStar_All.pipe_right uu____5833
           (FStar_List.filter FStar_Util.file_exists)
          in
       let uu____5846 =
         let uu____5849 = get_include ()  in
         FStar_List.append uu____5849 ["."]  in
       FStar_List.append uu____5830 uu____5846)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  fun filename  ->
    let uu____5859 = FStar_Util.is_path_absolute filename  in
    if uu____5859
    then
      (if FStar_Util.file_exists filename
       then FStar_Pervasives_Native.Some filename
       else FStar_Pervasives_Native.None)
    else
      (let uu____5866 =
         let uu____5869 = include_path ()  in FStar_List.rev uu____5869  in
       FStar_Util.find_map uu____5866
         (fun p  ->
            let path =
              if p = "." then filename else FStar_Util.join_paths p filename
               in
            if FStar_Util.file_exists path
            then FStar_Pervasives_Native.Some path
            else FStar_Pervasives_Native.None))
  
let (prims : unit -> Prims.string) =
  fun uu____5884  ->
    let uu____5885 = get_prims ()  in
    match uu____5885 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____5889 = find_file filename  in
        (match uu____5889 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____5893 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____5893)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____5899  ->
    let uu____5900 = prims ()  in FStar_Util.basename uu____5900
  
let (pervasives : unit -> Prims.string) =
  fun uu____5905  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____5907 = find_file filename  in
    match uu____5907 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____5911 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5911
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____5916  ->
    let uu____5917 = pervasives ()  in FStar_Util.basename uu____5917
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____5922  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____5924 = find_file filename  in
    match uu____5924 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____5928 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____5928
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____5934 = get_odir ()  in
    match uu____5934 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____5943 = get_cache_dir ()  in
    match uu____5943 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____5947 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____5947
  
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
             let uu____5995 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             FStar_Ident.path_of_text uu____5995  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           let uu____5999 = FStar_Ident.path_of_text s1  in
           (uu____5999, true))
       in
    let uu____6000 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6000 FStar_List.rev
  
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
let (cache_off : unit -> Prims.bool) = fun uu____6095  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6101 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6107 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6113 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6119 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6126  ->
    let uu____6127 = get_codegen ()  in
    FStar_Util.map_opt uu____6127
      (fun uu___72_6131  ->
         match uu___72_6131 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6132 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6141  ->
    let uu____6142 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6142
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6159  -> let uu____6160 = get_debug ()  in uu____6160 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6170 = get_debug ()  in
    FStar_All.pipe_right uu____6170 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6187 = get_debug ()  in
       FStar_All.pipe_right uu____6187 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6196  -> let uu____6197 = get_defensive ()  in uu____6197 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6202  ->
    let uu____6203 = get_defensive ()  in uu____6203 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6210  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6215  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6220  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6225  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6231 = get_dump_module ()  in
    FStar_All.pipe_right uu____6231 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6240  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6245  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6251 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6251
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6285  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6290  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6295  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6302  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6307  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6312  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6317  ->
    let uu____6318 = get_initial_fuel ()  in
    let uu____6319 = get_max_fuel ()  in Prims.min uu____6318 uu____6319
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6324  ->
    let uu____6325 = get_initial_ifuel ()  in
    let uu____6326 = get_max_ifuel ()  in Prims.min uu____6325 uu____6326
  
let (interactive : unit -> Prims.bool) =
  fun uu____6331  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6336  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6343  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6348  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6353  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6358  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6363  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6368  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6373  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6378  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6383  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6388  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6393  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6400 = get_no_extract ()  in
    FStar_All.pipe_right uu____6400
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6411  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6416  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6421  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6428  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6433  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6438  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6443  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6448  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6453  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6458  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6463  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____6468  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____6473  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6480  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____6485  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6490  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6495  ->
    let uu____6496 = get_smtencoding_nl_arith_repr ()  in
    uu____6496 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6501  ->
    let uu____6502 = get_smtencoding_nl_arith_repr ()  in
    uu____6502 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6507  ->
    let uu____6508 = get_smtencoding_nl_arith_repr ()  in
    uu____6508 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6513  ->
    let uu____6514 = get_smtencoding_l_arith_repr ()  in
    uu____6514 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6519  ->
    let uu____6520 = get_smtencoding_l_arith_repr ()  in
    uu____6520 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6525  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6530  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6535  -> get_tactic_trace_d () 
let (timing : unit -> Prims.bool) = fun uu____6540  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____6545  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____6550  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____6555  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____6560  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____6565  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____6570  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6577  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____6582  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (FStar_Ident.path,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____6593  ->
    let uu____6594 = get_using_facts_from ()  in
    match uu____6594 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____6624  ->
    let uu____6625 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____6625
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____6632  ->
    let uu____6633 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____6633 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____6636 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____6643  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____6648  ->
    let uu____6649 = get_smt ()  in
    match uu____6649 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____6659  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____6664  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____6669  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____6674  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____6679  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____6684  ->
    (get_use_two_phase_tc ()) &&
      (let uu____6686 = lax ()  in Prims.op_Negation uu____6686)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____6691  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____6696  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____6701  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____6706  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____6713 = get_extract ()  in
    match uu____6713 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____6724 =
            let uu____6737 = get_no_extract ()  in
            let uu____6740 = get_extract_namespace ()  in
            let uu____6743 = get_extract_module ()  in
            (uu____6737, uu____6740, uu____6743)  in
          match uu____6724 with
          | ([],[],[]) -> ()
          | uu____6758 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = FStar_Ident.path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____6804,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____6823 -> false  in
          let uu____6832 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____6866  ->
                    match uu____6866 with
                    | (path,uu____6874) -> matches_path m_components path))
             in
          match uu____6832 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____6885,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____6905 = get_extract_namespace ()  in
          match uu____6905 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____6921 = get_extract_module ()  in
          match uu____6921 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____6933 = no_extract m1  in Prims.op_Negation uu____6933) &&
          (let uu____6935 =
             let uu____6944 = get_extract_namespace ()  in
             let uu____6947 = get_extract_module ()  in
             (uu____6944, uu____6947)  in
           (match uu____6935 with
            | ([],[]) -> true
            | uu____6958 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  