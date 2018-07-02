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
  fun uu___73_284  ->
    match uu___73_284 with
    | Bool b -> b
    | uu____286 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___74_291  ->
    match uu___74_291 with
    | Int b -> b
    | uu____293 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___75_298  ->
    match uu___75_298 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____301 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___76_308  ->
    match uu___76_308 with
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
    fun uu___77_369  ->
      match uu___77_369 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____373 = as_t v1  in FStar_Pervasives_Native.Some uu____373
  
type optionstate = option_val FStar_Util.smap
let (fstar_options : optionstate Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : unit -> optionstate) =
  fun uu____397  ->
    let uu____398 = FStar_ST.op_Bang fstar_options  in
    FStar_List.hd uu____398
  
let (pop : unit -> unit) =
  fun uu____428  ->
    let uu____429 = FStar_ST.op_Bang fstar_options  in
    match uu____429 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____455::[] -> failwith "TOO MANY POPS!"
    | uu____456::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____487  ->
    let uu____488 =
      let uu____491 =
        let uu____492 = peek ()  in FStar_Util.smap_copy uu____492  in
      let uu____495 = FStar_ST.op_Bang fstar_options  in uu____491 ::
        uu____495
       in
    FStar_ST.op_Colon_Equals fstar_options uu____488
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____549 = FStar_ST.op_Bang fstar_options  in
    match uu____549 with
    | [] -> failwith "set on empty option stack"
    | uu____575::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
  
let (snapshot : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____610  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  -> let uu____630 = peek ()  in FStar_Util.smap_add uu____630 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____641  -> match uu____641 with | (k,v1) -> set_option k v1 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f ()  in pop (); retv) 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____688 =
      let uu____691 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____691
       in
    FStar_ST.op_Colon_Equals light_off_files uu____688
  
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
  fun uu____1134  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1151  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1208 =
      let uu____1211 = peek ()  in FStar_Util.smap_try_find uu____1211 s  in
    match uu____1208 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1221 . Prims.string -> (option_val -> 'Auu____1221) -> 'Auu____1221
  = fun s  -> fun c  -> let uu____1237 = get_option s  in c uu____1237 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1242  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1249  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1256  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1263  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1270  -> lookup_opt "cache_off" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1277  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1286  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1295  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1304  -> lookup_opt "debug_level" (as_list as_string) 
let (get_defensive : unit -> Prims.string) =
  fun uu____1311  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1318  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1325  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1330  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1335  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1342  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1349  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1354  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1363  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1376  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1385  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1392  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1397  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1402  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1409  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1416  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1421  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1428  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1435  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1440  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1445  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1450  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1457  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1464  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1469  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1474  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1479  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1484  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1489  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1494  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1499  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1506  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1513  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1518  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1523  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1530  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1537  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1544  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1551  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1556  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1561  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1566  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1571  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1576  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1581  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1586  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1591  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1598  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1605  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1612  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1619  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1624  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1629  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1634  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1639  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1644  -> lookup_opt "tactic_trace_d" as_int 
let (get_timing : unit -> Prims.bool) =
  fun uu____1649  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1654  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1659  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1664  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1669  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1674  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1679  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1686  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1693  ->
    let uu____1694 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1694
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1703  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1716  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1725  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1734  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1741  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1746  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1753  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1760  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1765  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1770  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1775  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1780  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1785  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1790  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1795  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1800  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___78_1805  ->
    match uu___78_1805 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1817 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1823 = get_debug_level ()  in
    FStar_All.pipe_right uu____1823
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____1956  ->
    let uu____1957 =
      let uu____1958 = FStar_ST.op_Bang _version  in
      let uu____1978 = FStar_ST.op_Bang _platform  in
      let uu____1998 = FStar_ST.op_Bang _compiler  in
      let uu____2018 = FStar_ST.op_Bang _date  in
      let uu____2038 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____1958
        uu____1978 uu____1998 uu____2018 uu____2038
       in
    FStar_Util.print_string uu____1957
  
let display_usage_aux :
  'Auu____2064 'Auu____2065 .
    ('Auu____2064,Prims.string,'Auu____2065 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2113  ->
         match uu____2113 with
         | (uu____2124,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2136 =
                      let uu____2137 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2137  in
                    FStar_Util.print_string uu____2136
                  else
                    (let uu____2139 =
                       let uu____2140 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2140 doc  in
                     FStar_Util.print_string uu____2139)
              | FStar_Getopt.OneArg (uu____2141,argname) ->
                  if doc = ""
                  then
                    let uu____2149 =
                      let uu____2150 = FStar_Util.colorize_bold flag  in
                      let uu____2151 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2150 uu____2151
                       in
                    FStar_Util.print_string uu____2149
                  else
                    (let uu____2153 =
                       let uu____2154 = FStar_Util.colorize_bold flag  in
                       let uu____2155 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2154
                         uu____2155 doc
                        in
                     FStar_Util.print_string uu____2153))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2183 = o  in
    match uu____2183 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2219 =
                let uu____2220 = f ()  in set_option name uu____2220  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2235 = f x  in set_option name uu____2235
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2255 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2255  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2278 =
        let uu____2281 = lookup_opt name as_list'  in
        FStar_List.append uu____2281 [value]  in
      mk_list uu____2278
  
let accumulate_string :
  'Auu____2294 .
    Prims.string -> ('Auu____2294 -> Prims.string) -> 'Auu____2294 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2315 =
          let uu____2316 =
            let uu____2317 = post_processor value  in mk_string uu____2317
             in
          accumulated_option name uu____2316  in
        set_option name uu____2315
  
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
    match projectee with | Const _0 -> true | uu____2413 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2427 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2440 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2447 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2461 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2477 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2503 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2542 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2577 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2591 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2612 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2650 -> true
    | uu____2651 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2658 -> uu____2658
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___82_2676  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____2678 ->
                      let uu____2679 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____2679 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____2683 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____2683
                  | PathStr uu____2686 -> mk_path str_val
                  | SimpleStr uu____2687 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____2692 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____2707 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____2707
                  | Accumulated elem_spec ->
                      let v1 = parse_opt_val opt_name elem_spec str_val  in
                      accumulated_option opt_name v1
                  | ReverseAccumulated elem_spec ->
                      let v1 = parse_opt_val opt_name elem_spec str_val  in
                      reverse_accumulated_option opt_name v1
                  | WithSideEffect (side_effect,elem_spec) ->
                      (side_effect ();
                       parse_opt_val opt_name elem_spec str_val))) ()
        with
        | InvalidArgument opt_name1 ->
            let uu____2726 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2726
  
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
    | PostProcessed (uu____2763,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2773,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2800 = desc_of_opt_type typ  in
      match uu____2800 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2806  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2823 =
      let uu____2824 = as_string s  in FStar_String.lowercase uu____2824  in
    mk_string uu____2823
  
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2846  ->
    let uu____2858 =
      let uu____2870 =
        let uu____2882 =
          let uu____2892 = let uu____2893 = mk_bool true  in Const uu____2893
             in
          (FStar_Getopt.noshort, "cache_checked_modules", uu____2892,
            "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
           in
        let uu____2895 =
          let uu____2907 =
            let uu____2919 =
              let uu____2929 =
                let uu____2930 = mk_bool true  in Const uu____2930  in
              (FStar_Getopt.noshort, "cache_off", uu____2929,
                "Do not read or write any .checked files")
               in
            let uu____2932 =
              let uu____2944 =
                let uu____2956 =
                  let uu____2968 =
                    let uu____2980 =
                      let uu____2992 =
                        let uu____3004 =
                          let uu____3016 =
                            let uu____3026 =
                              let uu____3027 = mk_bool true  in
                              Const uu____3027  in
                            (FStar_Getopt.noshort, "detail_errors",
                              uu____3026,
                              "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                             in
                          let uu____3029 =
                            let uu____3041 =
                              let uu____3051 =
                                let uu____3052 = mk_bool true  in
                                Const uu____3052  in
                              (FStar_Getopt.noshort, "detail_hint_replay",
                                uu____3051,
                                "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                               in
                            let uu____3054 =
                              let uu____3066 =
                                let uu____3076 =
                                  let uu____3077 = mk_bool true  in
                                  Const uu____3077  in
                                (FStar_Getopt.noshort, "doc", uu____3076,
                                  "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                 in
                              let uu____3079 =
                                let uu____3091 =
                                  let uu____3103 =
                                    let uu____3113 =
                                      let uu____3114 = mk_bool true  in
                                      Const uu____3114  in
                                    (FStar_Getopt.noshort, "eager_inference",
                                      uu____3113,
                                      "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                     in
                                  let uu____3116 =
                                    let uu____3128 =
                                      let uu____3138 =
                                        let uu____3139 = mk_bool true  in
                                        Const uu____3139  in
                                      (FStar_Getopt.noshort,
                                        "eager_subtyping", uu____3138,
                                        "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                       in
                                    let uu____3141 =
                                      let uu____3153 =
                                        let uu____3165 =
                                          let uu____3177 =
                                            let uu____3189 =
                                              let uu____3199 =
                                                let uu____3200 = mk_bool true
                                                   in
                                                Const uu____3200  in
                                              (FStar_Getopt.noshort,
                                                "expose_interfaces",
                                                uu____3199,
                                                "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                               in
                                            let uu____3202 =
                                              let uu____3214 =
                                                let uu____3224 =
                                                  let uu____3225 =
                                                    mk_bool true  in
                                                  Const uu____3225  in
                                                (FStar_Getopt.noshort,
                                                  "hide_uvar_nums",
                                                  uu____3224,
                                                  "Don't print unification variable numbers")
                                                 in
                                              let uu____3227 =
                                                let uu____3239 =
                                                  let uu____3251 =
                                                    let uu____3261 =
                                                      let uu____3262 =
                                                        mk_bool true  in
                                                      Const uu____3262  in
                                                    (FStar_Getopt.noshort,
                                                      "hint_info",
                                                      uu____3261,
                                                      "Print information regarding hints (deprecated; use --query_stats instead)")
                                                     in
                                                  let uu____3264 =
                                                    let uu____3276 =
                                                      let uu____3286 =
                                                        let uu____3287 =
                                                          mk_bool true  in
                                                        Const uu____3287  in
                                                      (FStar_Getopt.noshort,
                                                        "in", uu____3286,
                                                        "Legacy interactive mode; reads input from stdin")
                                                       in
                                                    let uu____3289 =
                                                      let uu____3301 =
                                                        let uu____3311 =
                                                          let uu____3312 =
                                                            mk_bool true  in
                                                          Const uu____3312
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "ide", uu____3311,
                                                          "JSON-based interactive mode for IDEs")
                                                         in
                                                      let uu____3314 =
                                                        let uu____3326 =
                                                          let uu____3338 =
                                                            let uu____3348 =
                                                              let uu____3349
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____3349
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "indent",
                                                              uu____3348,
                                                              "Parses and outputs the files on the command line")
                                                             in
                                                          let uu____3351 =
                                                            let uu____3363 =
                                                              let uu____3375
                                                                =
                                                                let uu____3387
                                                                  =
                                                                  let uu____3397
                                                                    =
                                                                    let uu____3398
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3398
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3397,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                   in
                                                                let uu____3400
                                                                  =
                                                                  let uu____3412
                                                                    =
                                                                    let uu____3424
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
                                                                    let uu____3437
                                                                    =
                                                                    let uu____3449
                                                                    =
                                                                    let uu____3459
                                                                    =
                                                                    let uu____3460
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3460
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3459,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3462
                                                                    =
                                                                    let uu____3474
                                                                    =
                                                                    let uu____3486
                                                                    =
                                                                    let uu____3498
                                                                    =
                                                                    let uu____3510
                                                                    =
                                                                    let uu____3520
                                                                    =
                                                                    let uu____3521
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3521
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3520,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3523
                                                                    =
                                                                    let uu____3535
                                                                    =
                                                                    let uu____3547
                                                                    =
                                                                    let uu____3557
                                                                    =
                                                                    let uu____3558
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3558
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3557,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3560
                                                                    =
                                                                    let uu____3572
                                                                    =
                                                                    let uu____3584
                                                                    =
                                                                    let uu____3594
                                                                    =
                                                                    let uu____3595
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3595
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3594,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3597
                                                                    =
                                                                    let uu____3609
                                                                    =
                                                                    let uu____3619
                                                                    =
                                                                    let uu____3620
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3620
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3619,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3622
                                                                    =
                                                                    let uu____3634
                                                                    =
                                                                    let uu____3644
                                                                    =
                                                                    let uu____3645
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3645
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3644,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3647
                                                                    =
                                                                    let uu____3659
                                                                    =
                                                                    let uu____3671
                                                                    =
                                                                    let uu____3683
                                                                    =
                                                                    let uu____3693
                                                                    =
                                                                    let uu____3694
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3694
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____3693,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3696
                                                                    =
                                                                    let uu____3708
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
                                                                    let uu____3721
                                                                    =
                                                                    let uu____3733
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
                                                                    "print_full_names",
                                                                    uu____3743,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3746
                                                                    =
                                                                    let uu____3758
                                                                    =
                                                                    let uu____3768
                                                                    =
                                                                    let uu____3769
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3769
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3768,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3771
                                                                    =
                                                                    let uu____3783
                                                                    =
                                                                    let uu____3793
                                                                    =
                                                                    let uu____3794
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3794
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3793,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3796
                                                                    =
                                                                    let uu____3808
                                                                    =
                                                                    let uu____3818
                                                                    =
                                                                    let uu____3819
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3819
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____3818,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____3821
                                                                    =
                                                                    let uu____3833
                                                                    =
                                                                    let uu____3843
                                                                    =
                                                                    let uu____3844
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3844
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____3843,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____3846
                                                                    =
                                                                    let uu____3858
                                                                    =
                                                                    let uu____3868
                                                                    =
                                                                    let uu____3869
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3869
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____3868,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____3871
                                                                    =
                                                                    let uu____3883
                                                                    =
                                                                    let uu____3893
                                                                    =
                                                                    let uu____3894
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3894
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____3893,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____3896
                                                                    =
                                                                    let uu____3908
                                                                    =
                                                                    let uu____3920
                                                                    =
                                                                    let uu____3930
                                                                    =
                                                                    let uu____3931
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3931
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____3930,
                                                                    " ")  in
                                                                    let uu____3933
                                                                    =
                                                                    let uu____3945
                                                                    =
                                                                    let uu____3957
                                                                    =
                                                                    let uu____3969
                                                                    =
                                                                    let uu____3981
                                                                    =
                                                                    let uu____3993
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
                                                                    "tactic_raw_binders",
                                                                    uu____4003,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4006
                                                                    =
                                                                    let uu____4018
                                                                    =
                                                                    let uu____4028
                                                                    =
                                                                    let uu____4029
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4029
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4028,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4031
                                                                    =
                                                                    let uu____4043
                                                                    =
                                                                    let uu____4055
                                                                    =
                                                                    let uu____4065
                                                                    =
                                                                    let uu____4066
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4066
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4065,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4068
                                                                    =
                                                                    let uu____4080
                                                                    =
                                                                    let uu____4090
                                                                    =
                                                                    let uu____4091
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4091
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4090,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4093
                                                                    =
                                                                    let uu____4105
                                                                    =
                                                                    let uu____4115
                                                                    =
                                                                    let uu____4116
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4116
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4115,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4118
                                                                    =
                                                                    let uu____4130
                                                                    =
                                                                    let uu____4140
                                                                    =
                                                                    let uu____4141
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4141
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4140,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4143
                                                                    =
                                                                    let uu____4155
                                                                    =
                                                                    let uu____4165
                                                                    =
                                                                    let uu____4166
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4166
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4165,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4168
                                                                    =
                                                                    let uu____4180
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
                                                                    "use_eq_at_higher_order",
                                                                    uu____4190,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4193
                                                                    =
                                                                    let uu____4205
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
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4215,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4218
                                                                    =
                                                                    let uu____4230
                                                                    =
                                                                    let uu____4240
                                                                    =
                                                                    let uu____4241
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4241
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4240,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4243
                                                                    =
                                                                    let uu____4255
                                                                    =
                                                                    let uu____4267
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
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4277,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4280
                                                                    =
                                                                    let uu____4292
                                                                    =
                                                                    let uu____4304
                                                                    =
                                                                    let uu____4316
                                                                    =
                                                                    let uu____4328
                                                                    =
                                                                    let uu____4338
                                                                    =
                                                                    let uu____4339
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4339
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4338,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4341
                                                                    =
                                                                    let uu____4353
                                                                    =
                                                                    let uu____4363
                                                                    =
                                                                    let uu____4364
                                                                    =
                                                                    let uu____4372
                                                                    =
                                                                    let uu____4373
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4373
                                                                     in
                                                                    ((fun
                                                                    uu____4379
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4372)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4364
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4363,
                                                                    "Display version number")
                                                                     in
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
                                                                    "warn_default_effects",
                                                                    uu____4405,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4408
                                                                    =
                                                                    let uu____4420
                                                                    =
                                                                    let uu____4432
                                                                    =
                                                                    let uu____4442
                                                                    =
                                                                    let uu____4443
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4443
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4442,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4445
                                                                    =
                                                                    let uu____4457
                                                                    =
                                                                    let uu____4469
                                                                    =
                                                                    let uu____4481
                                                                    =
                                                                    let uu____4493
                                                                    =
                                                                    let uu____4505
                                                                    =
                                                                    let uu____4515
                                                                    =
                                                                    let uu____4516
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4516
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4515,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4518
                                                                    =
                                                                    let uu____4530
                                                                    =
                                                                    let uu____4540
                                                                    =
                                                                    let uu____4541
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4541
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4540,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4543
                                                                    =
                                                                    let uu____4555
                                                                    =
                                                                    let uu____4567
                                                                    =
                                                                    let uu____4579
                                                                    =
                                                                    let uu____4589
                                                                    =
                                                                    let uu____4590
                                                                    =
                                                                    let uu____4598
                                                                    =
                                                                    let uu____4599
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4599
                                                                     in
                                                                    ((fun
                                                                    uu____4605
                                                                     ->
                                                                    (
                                                                    let uu____4607
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4607);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4598)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4590
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4589,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4579]
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4567
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4555
                                                                     in
                                                                    uu____4530
                                                                    ::
                                                                    uu____4543
                                                                     in
                                                                    uu____4505
                                                                    ::
                                                                    uu____4518
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4493
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4481
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4469
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4457
                                                                     in
                                                                    uu____4432
                                                                    ::
                                                                    uu____4445
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4420
                                                                     in
                                                                    uu____4395
                                                                    ::
                                                                    uu____4408
                                                                     in
                                                                    uu____4353
                                                                    ::
                                                                    uu____4383
                                                                     in
                                                                    uu____4328
                                                                    ::
                                                                    uu____4341
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4316
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4304
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4292
                                                                     in
                                                                    uu____4267
                                                                    ::
                                                                    uu____4280
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4255
                                                                     in
                                                                    uu____4230
                                                                    ::
                                                                    uu____4243
                                                                     in
                                                                    uu____4205
                                                                    ::
                                                                    uu____4218
                                                                     in
                                                                    uu____4180
                                                                    ::
                                                                    uu____4193
                                                                     in
                                                                    uu____4155
                                                                    ::
                                                                    uu____4168
                                                                     in
                                                                    uu____4130
                                                                    ::
                                                                    uu____4143
                                                                     in
                                                                    uu____4105
                                                                    ::
                                                                    uu____4118
                                                                     in
                                                                    uu____4080
                                                                    ::
                                                                    uu____4093
                                                                     in
                                                                    uu____4055
                                                                    ::
                                                                    uu____4068
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4043
                                                                     in
                                                                    uu____4018
                                                                    ::
                                                                    uu____4031
                                                                     in
                                                                    uu____3993
                                                                    ::
                                                                    uu____4006
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3981
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____3969
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____3957
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____3945
                                                                     in
                                                                    uu____3920
                                                                    ::
                                                                    uu____3933
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____3908
                                                                     in
                                                                    uu____3883
                                                                    ::
                                                                    uu____3896
                                                                     in
                                                                    uu____3858
                                                                    ::
                                                                    uu____3871
                                                                     in
                                                                    uu____3833
                                                                    ::
                                                                    uu____3846
                                                                     in
                                                                    uu____3808
                                                                    ::
                                                                    uu____3821
                                                                     in
                                                                    uu____3783
                                                                    ::
                                                                    uu____3796
                                                                     in
                                                                    uu____3758
                                                                    ::
                                                                    uu____3771
                                                                     in
                                                                    uu____3733
                                                                    ::
                                                                    uu____3746
                                                                     in
                                                                    uu____3708
                                                                    ::
                                                                    uu____3721
                                                                     in
                                                                    uu____3683
                                                                    ::
                                                                    uu____3696
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3671
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3659
                                                                     in
                                                                    uu____3634
                                                                    ::
                                                                    uu____3647
                                                                     in
                                                                    uu____3609
                                                                    ::
                                                                    uu____3622
                                                                     in
                                                                    uu____3584
                                                                    ::
                                                                    uu____3597
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3572
                                                                     in
                                                                    uu____3547
                                                                    ::
                                                                    uu____3560
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3535
                                                                     in
                                                                    uu____3510
                                                                    ::
                                                                    uu____3523
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3498
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3486
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3474
                                                                     in
                                                                    uu____3449
                                                                    ::
                                                                    uu____3462
                                                                     in
                                                                    uu____3424
                                                                    ::
                                                                    uu____3437
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (
                                                                    ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3412
                                                                   in
                                                                uu____3387 ::
                                                                  uu____3400
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_ifuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                :: uu____3375
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "initial_fuel",
                                                              (IntStr
                                                                 "non-negative integer"),
                                                              "Number of unrolling of recursive functions to try initially (default 2)")
                                                              :: uu____3363
                                                             in
                                                          uu____3338 ::
                                                            uu____3351
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "include",
                                                          (ReverseAccumulated
                                                             (PathStr "path")),
                                                          "A directory in which to search for files included on the command line")
                                                          :: uu____3326
                                                         in
                                                      uu____3301 ::
                                                        uu____3314
                                                       in
                                                    uu____3276 :: uu____3289
                                                     in
                                                  uu____3251 :: uu____3264
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "hint_file",
                                                  (PathStr "path"),
                                                  "Read/write hints to <path> (instead of module-specific hints files)")
                                                  :: uu____3239
                                                 in
                                              uu____3214 :: uu____3227  in
                                            uu____3189 :: uu____3202  in
                                          (FStar_Getopt.noshort,
                                            "extract_namespace",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr
                                                       "namespace name")))),
                                            "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                            :: uu____3177
                                           in
                                        (FStar_Getopt.noshort,
                                          "extract_module",
                                          (Accumulated
                                             (PostProcessed
                                                (pp_lowercase,
                                                  (SimpleStr "module_name")))),
                                          "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                          :: uu____3165
                                         in
                                      (FStar_Getopt.noshort, "extract",
                                        (Accumulated
                                           (SimpleStr
                                              "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                        "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                        :: uu____3153
                                       in
                                    uu____3128 :: uu____3141  in
                                  uu____3103 :: uu____3116  in
                                (FStar_Getopt.noshort, "dump_module",
                                  (Accumulated (SimpleStr "module_name")),
                                  "") :: uu____3091
                                 in
                              uu____3066 :: uu____3079  in
                            uu____3041 :: uu____3054  in
                          uu____3016 :: uu____3029  in
                        (FStar_Getopt.noshort, "dep",
                          (EnumStr ["make"; "graph"; "full"]),
                          "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                          :: uu____3004
                         in
                      (FStar_Getopt.noshort, "defensive",
                        (EnumStr ["no"; "warn"; "fail"]),
                        "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                        :: uu____2992
                       in
                    (FStar_Getopt.noshort, "debug_level",
                      (Accumulated
                         (OpenEnumStr
                            (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                      "Control the verbosity of debugging info") ::
                      uu____2980
                     in
                  (FStar_Getopt.noshort, "debug",
                    (Accumulated (SimpleStr "module_name")),
                    "Print lots of debugging information while checking module")
                    :: uu____2968
                   in
                (FStar_Getopt.noshort, "codegen-lib",
                  (Accumulated (SimpleStr "namespace")),
                  "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                  :: uu____2956
                 in
              (FStar_Getopt.noshort, "codegen",
                (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                "Generate code for further compilation to executable code, or build a compiler plugin")
                :: uu____2944
               in
            uu____2919 :: uu____2932  in
          (FStar_Getopt.noshort, "cache_dir",
            (PostProcessed (pp_validate_dir, (PathStr "dir"))),
            "Read and write .checked and .checked.lax in directory <dir>") ::
            uu____2907
           in
        uu____2882 :: uu____2895  in
      (FStar_Getopt.noshort, "admit_except",
        (SimpleStr "[symbol|(symbol, id)]"),
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
        :: uu____2870
       in
    (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
      "Admit SMT queries, unsafe! (default 'false')") :: uu____2858

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5508  ->
    let uu____5511 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5538  ->
         match uu____5538 with
         | (short,long,typ,doc) ->
             let uu____5554 =
               let uu____5566 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5566, doc)  in
             mk_spec uu____5554) uu____5511

let (settable : Prims.string -> Prims.bool) =
  fun uu___79_5576  ->
    match uu___79_5576 with
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
    | uu____5577 -> false
  
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
       (fun uu____5651  ->
          match uu____5651 with
          | (uu____5663,x,uu____5665,uu____5666) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5728  ->
          match uu____5728 with
          | (uu____5740,x,uu____5742,uu____5743) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5754  ->
    let uu____5755 = specs ()  in display_usage_aux uu____5755
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____5779 -> true
    | uu____5780 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____5787 -> uu____5787
  
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
        (fun uu___84_5804  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____5815 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____5815
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____5843  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____5848 =
             let uu____5851 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____5851 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____5848)
       in
    let uu____5900 =
      let uu____5903 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____5903
       in
    (res, uu____5900)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____5937  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____5972 = specs ()  in
       FStar_Getopt.parse_cmdline uu____5972 (fun x  -> ())  in
     (let uu____5978 =
        let uu____5983 =
          let uu____5984 = FStar_List.map mk_string old_verify_module  in
          List uu____5984  in
        ("verify_module", uu____5983)  in
      set_option' uu____5978);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____5994 =
        let uu____5995 =
          let uu____5996 =
            let uu____5997 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____5997  in
          (FStar_String.length f1) - uu____5996  in
        uu____5995 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____5994  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6003 = get_lax ()  in
    if uu____6003
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6013 = module_name_of_file_name fn  in should_verify uu____6013
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6019 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6019
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6027 = should_verify m  in
    if uu____6027 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6035  ->
    let uu____6036 = get_no_default_includes ()  in
    if uu____6036
    then get_include ()
    else
      (let lib_paths =
         let uu____6043 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6043 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6052 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6052
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6066 =
         let uu____6069 = get_include ()  in
         FStar_List.append uu____6069 ["."]  in
       FStar_List.append lib_paths uu____6066)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____6082 = FStar_Util.smap_try_find file_map filename  in
    match uu____6082 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___86_6095  ->
               match () with
               | () ->
                   let uu____6098 = FStar_Util.is_path_absolute filename  in
                   if uu____6098
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____6105 =
                        let uu____6108 = include_path ()  in
                        FStar_List.rev uu____6108  in
                      FStar_Util.find_map uu____6105
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu____6124 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____6133  ->
    let uu____6134 = get_prims ()  in
    match uu____6134 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6138 = find_file filename  in
        (match uu____6138 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6142 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6142)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6148  ->
    let uu____6149 = prims ()  in FStar_Util.basename uu____6149
  
let (pervasives : unit -> Prims.string) =
  fun uu____6154  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____6156 = find_file filename  in
    match uu____6156 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____6160 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6160
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6165  ->
    let uu____6166 = pervasives ()  in FStar_Util.basename uu____6166
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6171  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____6173 = find_file filename  in
    match uu____6173 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____6177 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6177
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____6183 = get_odir ()  in
    match uu____6183 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____6192 = get_cache_dir ()  in
    match uu____6192 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6196 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____6196
  
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
             let uu____6262 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____6262  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____6270 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6270 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6340 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6340 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6349  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6354  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6361  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6366  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____6371  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6377 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6383 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6389 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6395 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6402  ->
    let uu____6403 = get_codegen ()  in
    FStar_Util.map_opt uu____6403
      (fun uu___80_6407  ->
         match uu___80_6407 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6408 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6417  ->
    let uu____6418 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6418
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6435  -> let uu____6436 = get_debug ()  in uu____6436 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6446 = get_debug ()  in
    FStar_All.pipe_right uu____6446 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6463 = get_debug ()  in
       FStar_All.pipe_right uu____6463 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6472  -> let uu____6473 = get_defensive ()  in uu____6473 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6478  ->
    let uu____6479 = get_defensive ()  in uu____6479 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6486  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6491  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6496  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6501  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6507 = get_dump_module ()  in
    FStar_All.pipe_right uu____6507 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6516  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6521  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6527 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6527
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6557  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6562  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6567  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6574  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6579  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6584  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6589  ->
    let uu____6590 = get_initial_fuel ()  in
    let uu____6591 = get_max_fuel ()  in Prims.min uu____6590 uu____6591
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6596  ->
    let uu____6597 = get_initial_ifuel ()  in
    let uu____6598 = get_max_ifuel ()  in Prims.min uu____6597 uu____6598
  
let (interactive : unit -> Prims.bool) =
  fun uu____6603  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6608  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6615  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6620  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6625  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6630  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6635  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6640  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6645  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6650  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6655  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6660  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6665  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6672 = get_no_extract ()  in
    FStar_All.pipe_right uu____6672
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6683  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6688  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6693  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6700  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6705  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6710  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6715  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6720  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6725  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6730  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____6735  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____6740  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____6745  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6752  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____6757  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____6762  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____6767  ->
    let uu____6768 = get_smtencoding_nl_arith_repr ()  in
    uu____6768 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____6773  ->
    let uu____6774 = get_smtencoding_nl_arith_repr ()  in
    uu____6774 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____6779  ->
    let uu____6780 = get_smtencoding_nl_arith_repr ()  in
    uu____6780 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____6785  ->
    let uu____6786 = get_smtencoding_l_arith_repr ()  in
    uu____6786 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____6791  ->
    let uu____6792 = get_smtencoding_l_arith_repr ()  in
    uu____6792 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____6797  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____6802  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____6807  -> get_tactic_trace_d () 
let (timing : unit -> Prims.bool) = fun uu____6812  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____6817  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____6822  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____6827  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____6832  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____6837  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____6842  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6849  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____6854  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____6867  ->
    let uu____6868 = get_using_facts_from ()  in
    match uu____6868 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____6906  ->
    let uu____6907 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____6907
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____6914  ->
    let uu____6915 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____6915 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____6918 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____6925  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____6930  ->
    let uu____6931 = get_smt ()  in
    match uu____6931 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____6941  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____6946  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____6951  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____6956  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____6961  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____6966  ->
    (get_use_two_phase_tc ()) &&
      (let uu____6968 = lax ()  in Prims.op_Negation uu____6968)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____6973  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____6978  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____6983  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____6988  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____6995 = get_extract ()  in
    match uu____6995 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7006 =
            let uu____7019 = get_no_extract ()  in
            let uu____7022 = get_extract_namespace ()  in
            let uu____7025 = get_extract_module ()  in
            (uu____7019, uu____7022, uu____7025)  in
          match uu____7006 with
          | ([],[],[]) -> ()
          | uu____7040 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7088,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7107 -> false  in
          let uu____7116 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7150  ->
                    match uu____7150 with
                    | (path,uu____7158) -> matches_path m_components path))
             in
          match uu____7116 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____7169,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____7189 = get_extract_namespace ()  in
          match uu____7189 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____7205 = get_extract_module ()  in
          match uu____7205 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____7217 = no_extract m1  in Prims.op_Negation uu____7217) &&
          (let uu____7219 =
             let uu____7228 = get_extract_namespace ()  in
             let uu____7231 = get_extract_module ()  in
             (uu____7228, uu____7231)  in
           (match uu____7219 with
            | ([],[]) -> true
            | uu____7242 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  