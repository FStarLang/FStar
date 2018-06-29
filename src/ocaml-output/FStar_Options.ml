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
  fun uu___75_296  ->
    match uu___75_296 with
    | Bool b -> b
    | uu____298 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___76_303  ->
    match uu___76_303 with
    | Int b -> b
    | uu____305 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___77_310  ->
    match uu___77_310 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____313 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___78_320  ->
    match uu___78_320 with
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
    fun uu___79_381  ->
      match uu___79_381 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____385 = as_t v1  in FStar_Pervasives_Native.Some uu____385
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___80_392  ->
    match uu___80_392 with
    | List ls ->
        let uu____398 =
          FStar_List.map
            (fun l  ->
               let uu____408 = as_string l  in FStar_Util.split uu____408 ",")
            ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____398
    | uu____415 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let (fstar_options : optionstate Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : unit -> optionstate) =
  fun uu____441  ->
    let uu____442 = FStar_ST.op_Bang fstar_options  in
    FStar_List.hd uu____442
  
let (pop : unit -> unit) =
  fun uu____476  ->
    let uu____477 = FStar_ST.op_Bang fstar_options  in
    match uu____477 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____507::[] -> failwith "TOO MANY POPS!"
    | uu____508::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____543  ->
    let uu____544 =
      let uu____547 =
        let uu____548 = peek ()  in FStar_Util.smap_copy uu____548  in
      let uu____551 = FStar_ST.op_Bang fstar_options  in uu____547 ::
        uu____551
       in
    FStar_ST.op_Colon_Equals fstar_options uu____544
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____613 = FStar_ST.op_Bang fstar_options  in
    match uu____613 with
    | [] -> failwith "set on empty option stack"
    | uu____643::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
  
let (snapshot : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____682  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  -> let uu____702 = peek ()  in FStar_Util.smap_add uu____702 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____713  -> match uu____713 with | (k,v1) -> set_option k v1 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f ()  in pop (); retv) 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____760 =
      let uu____763 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____763
       in
    FStar_ST.op_Colon_Equals light_off_files uu____760
  
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
  ("eager_embedding", (Bool false));
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
  fun uu____1222  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1239  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [o];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1304 =
      let uu____1307 = peek ()  in FStar_Util.smap_try_find uu____1307 s  in
    match uu____1304 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1317 . Prims.string -> (option_val -> 'Auu____1317) -> 'Auu____1317
  = fun s  -> fun c  -> let uu____1333 = get_option s  in c uu____1333 
let (get_abort_on : unit -> Prims.int) =
  fun uu____1338  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1343  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1350  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1357  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1364  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1371  -> lookup_opt "cache_off" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1378  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1387  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1396  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1405  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____1412  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1419  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1426  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1431  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1436  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1443  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_embedding : unit -> Prims.bool) =
  fun uu____1450  -> lookup_opt "eager_embedding" as_bool 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1455  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1460  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1469  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1482  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1491  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1498  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1503  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1508  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1515  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1522  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1527  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1534  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1541  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1546  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1551  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1556  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1563  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1570  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1575  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1580  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1585  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1590  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1595  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1600  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1605  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1612  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1619  -> lookup_opt "no_location_info" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1624  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1629  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1636  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1643  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1650  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____1657  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____1662  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____1667  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____1672  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____1677  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____1682  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____1687  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____1692  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____1697  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1704  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____1711  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1718  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____1725  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____1730  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____1735  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____1740  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____1745  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____1750  -> lookup_opt "tactic_trace_d" as_int 
let (get_timing : unit -> Prims.bool) =
  fun uu____1755  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1760  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1765  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1770  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1775  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1780  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1785  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1792  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1799  ->
    let uu____1800 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1800
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1809  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1822  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1831  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1840  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1847  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1852  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1859  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1866  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1871  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1876  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1881  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1886  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1891  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1896  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1901  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1906  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___81_1911  ->
    match uu___81_1911 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1923 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1929 = get_debug_level ()  in
    FStar_All.pipe_right uu____1929
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2062  ->
    let uu____2063 =
      let uu____2064 = FStar_ST.op_Bang _version  in
      let uu____2088 = FStar_ST.op_Bang _platform  in
      let uu____2112 = FStar_ST.op_Bang _compiler  in
      let uu____2136 = FStar_ST.op_Bang _date  in
      let uu____2160 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2064
        uu____2088 uu____2112 uu____2136 uu____2160
       in
    FStar_Util.print_string uu____2063
  
let display_usage_aux :
  'Auu____2190 'Auu____2191 .
    ('Auu____2190,Prims.string,'Auu____2191 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2239  ->
         match uu____2239 with
         | (uu____2250,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2262 =
                      let uu____2263 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2263  in
                    FStar_Util.print_string uu____2262
                  else
                    (let uu____2265 =
                       let uu____2266 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2266 doc  in
                     FStar_Util.print_string uu____2265)
              | FStar_Getopt.OneArg (uu____2267,argname) ->
                  if doc = ""
                  then
                    let uu____2275 =
                      let uu____2276 = FStar_Util.colorize_bold flag  in
                      let uu____2277 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2276 uu____2277
                       in
                    FStar_Util.print_string uu____2275
                  else
                    (let uu____2279 =
                       let uu____2280 = FStar_Util.colorize_bold flag  in
                       let uu____2281 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2280
                         uu____2281 doc
                        in
                     FStar_Util.print_string uu____2279))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2309 = o  in
    match uu____2309 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2345 =
                let uu____2346 = f ()  in set_option name uu____2346  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2361 = f x  in set_option name uu____2361
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2381 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2381  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2404 =
        let uu____2407 = lookup_opt name as_list'  in
        FStar_List.append uu____2407 [value]  in
      mk_list uu____2404
  
let accumulate_string :
  'Auu____2420 .
    Prims.string -> ('Auu____2420 -> Prims.string) -> 'Auu____2420 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2441 =
          let uu____2442 =
            let uu____2443 = post_processor value  in mk_string uu____2443
             in
          accumulated_option name uu____2442  in
        set_option name uu____2441
  
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
    match projectee with | Const _0 -> true | uu____2539 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2553 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2566 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2573 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2587 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2603 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2629 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2668 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2703 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2717 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2738 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2776 -> true
    | uu____2777 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2784 -> uu____2784
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          match typ with
          | Const c -> c
          | IntStr uu____2804 ->
              let uu____2805 = FStar_Util.safe_int_of_string str_val  in
              (match uu____2805 with
               | FStar_Pervasives_Native.Some v1 -> mk_int v1
               | FStar_Pervasives_Native.None  ->
                   FStar_Exn.raise (InvalidArgument opt_name))
          | BoolStr  ->
              let uu____2809 =
                if str_val = "true"
                then true
                else
                  if str_val = "false"
                  then false
                  else FStar_Exn.raise (InvalidArgument opt_name)
                 in
              mk_bool uu____2809
          | PathStr uu____2812 -> mk_path str_val
          | SimpleStr uu____2813 -> mk_string str_val
          | EnumStr strs ->
              if FStar_List.mem str_val strs
              then mk_string str_val
              else FStar_Exn.raise (InvalidArgument opt_name)
          | OpenEnumStr uu____2818 -> mk_string str_val
          | PostProcessed (pp,elem_spec) ->
              let uu____2833 = parse_opt_val opt_name elem_spec str_val  in
              pp uu____2833
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
            let uu____2852 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2852
  
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
    | PostProcessed (uu____2889,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2899,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2926 = desc_of_opt_type typ  in
      match uu____2926 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2932  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2949 =
      let uu____2950 = as_string s  in FStar_String.lowercase uu____2950  in
    mk_string uu____2949
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2998  ->
    let uu____3010 =
      let uu____3022 =
        let uu____3034 =
          let uu____3046 =
            let uu____3056 =
              let uu____3057 = mk_bool true  in Const uu____3057  in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____3056,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
             in
          let uu____3059 =
            let uu____3071 =
              let uu____3083 =
                let uu____3093 =
                  let uu____3094 = mk_bool true  in Const uu____3094  in
                (FStar_Getopt.noshort, "cache_off", uu____3093,
                  "Do not read or write any .checked files")
                 in
              let uu____3096 =
                let uu____3108 =
                  let uu____3120 =
                    let uu____3132 =
                      let uu____3144 =
                        let uu____3156 =
                          let uu____3168 =
                            let uu____3180 =
                              let uu____3190 =
                                let uu____3191 = mk_bool true  in
                                Const uu____3191  in
                              (FStar_Getopt.noshort, "detail_errors",
                                uu____3190,
                                "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                               in
                            let uu____3193 =
                              let uu____3205 =
                                let uu____3215 =
                                  let uu____3216 = mk_bool true  in
                                  Const uu____3216  in
                                (FStar_Getopt.noshort, "detail_hint_replay",
                                  uu____3215,
                                  "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                 in
                              let uu____3218 =
                                let uu____3230 =
                                  let uu____3240 =
                                    let uu____3241 = mk_bool true  in
                                    Const uu____3241  in
                                  (FStar_Getopt.noshort, "doc", uu____3240,
                                    "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                   in
                                let uu____3243 =
                                  let uu____3255 =
                                    let uu____3267 =
                                      let uu____3277 =
                                        let uu____3278 = mk_bool true  in
                                        Const uu____3278  in
                                      (FStar_Getopt.noshort,
                                        "eager_embedding", uu____3277,
                                        "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                       in
                                    let uu____3280 =
                                      let uu____3292 =
                                        let uu____3302 =
                                          let uu____3303 = mk_bool true  in
                                          Const uu____3303  in
                                        (FStar_Getopt.noshort,
                                          "eager_inference", uu____3302,
                                          "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                         in
                                      let uu____3305 =
                                        let uu____3317 =
                                          let uu____3327 =
                                            let uu____3328 = mk_bool true  in
                                            Const uu____3328  in
                                          (FStar_Getopt.noshort,
                                            "eager_subtyping", uu____3327,
                                            "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                           in
                                        let uu____3330 =
                                          let uu____3342 =
                                            let uu____3354 =
                                              let uu____3366 =
                                                let uu____3378 =
                                                  let uu____3388 =
                                                    let uu____3389 =
                                                      mk_bool true  in
                                                    Const uu____3389  in
                                                  (FStar_Getopt.noshort,
                                                    "expose_interfaces",
                                                    uu____3388,
                                                    "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                   in
                                                let uu____3391 =
                                                  let uu____3403 =
                                                    let uu____3413 =
                                                      let uu____3414 =
                                                        mk_bool true  in
                                                      Const uu____3414  in
                                                    (FStar_Getopt.noshort,
                                                      "hide_uvar_nums",
                                                      uu____3413,
                                                      "Don't print unification variable numbers")
                                                     in
                                                  let uu____3416 =
                                                    let uu____3428 =
                                                      let uu____3440 =
                                                        let uu____3450 =
                                                          let uu____3451 =
                                                            mk_bool true  in
                                                          Const uu____3451
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "hint_info",
                                                          uu____3450,
                                                          "Print information regarding hints (deprecated; use --query_stats instead)")
                                                         in
                                                      let uu____3453 =
                                                        let uu____3465 =
                                                          let uu____3475 =
                                                            let uu____3476 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3476
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "in", uu____3475,
                                                            "Legacy interactive mode; reads input from stdin")
                                                           in
                                                        let uu____3478 =
                                                          let uu____3490 =
                                                            let uu____3500 =
                                                              let uu____3501
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____3501
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "ide",
                                                              uu____3500,
                                                              "JSON-based interactive mode for IDEs")
                                                             in
                                                          let uu____3503 =
                                                            let uu____3515 =
                                                              let uu____3527
                                                                =
                                                                let uu____3537
                                                                  =
                                                                  let uu____3538
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                  Const
                                                                    uu____3538
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "indent",
                                                                  uu____3537,
                                                                  "Parses and outputs the files on the command line")
                                                                 in
                                                              let uu____3540
                                                                =
                                                                let uu____3552
                                                                  =
                                                                  let uu____3564
                                                                    =
                                                                    let uu____3576
                                                                    =
                                                                    let uu____3586
                                                                    =
                                                                    let uu____3587
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3587
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3586,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____3589
                                                                    =
                                                                    let uu____3601
                                                                    =
                                                                    let uu____3613
                                                                    =
                                                                    let uu____3623
                                                                    =
                                                                    let uu____3624
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3624
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3623,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3626
                                                                    =
                                                                    let uu____3638
                                                                    =
                                                                    let uu____3648
                                                                    =
                                                                    let uu____3649
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3649
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3648,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3651
                                                                    =
                                                                    let uu____3663
                                                                    =
                                                                    let uu____3675
                                                                    =
                                                                    let uu____3687
                                                                    =
                                                                    let uu____3699
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
                                                                    "MLish",
                                                                    uu____3709,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3712
                                                                    =
                                                                    let uu____3724
                                                                    =
                                                                    let uu____3736
                                                                    =
                                                                    let uu____3746
                                                                    =
                                                                    let uu____3747
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3747
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____3746,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3749
                                                                    =
                                                                    let uu____3761
                                                                    =
                                                                    let uu____3773
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
                                                                    "no_location_info",
                                                                    uu____3783,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3786
                                                                    =
                                                                    let uu____3798
                                                                    =
                                                                    let uu____3808
                                                                    =
                                                                    let uu____3809
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3809
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3808,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3811
                                                                    =
                                                                    let uu____3823
                                                                    =
                                                                    let uu____3833
                                                                    =
                                                                    let uu____3834
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3834
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3833,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3836
                                                                    =
                                                                    let uu____3848
                                                                    =
                                                                    let uu____3860
                                                                    =
                                                                    let uu____3872
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
                                                                    "print_bound_var_types",
                                                                    uu____3882,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____3885
                                                                    =
                                                                    let uu____3897
                                                                    =
                                                                    let uu____3907
                                                                    =
                                                                    let uu____3908
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3908
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____3907,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____3910
                                                                    =
                                                                    let uu____3922
                                                                    =
                                                                    let uu____3932
                                                                    =
                                                                    let uu____3933
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3933
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____3932,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____3935
                                                                    =
                                                                    let uu____3947
                                                                    =
                                                                    let uu____3957
                                                                    =
                                                                    let uu____3958
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3958
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____3957,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____3960
                                                                    =
                                                                    let uu____3972
                                                                    =
                                                                    let uu____3982
                                                                    =
                                                                    let uu____3983
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3983
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____3982,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____3985
                                                                    =
                                                                    let uu____3997
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
                                                                    "print_z3_statistics",
                                                                    uu____4007,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____4010
                                                                    =
                                                                    let uu____4022
                                                                    =
                                                                    let uu____4032
                                                                    =
                                                                    let uu____4033
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4033
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____4032,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____4035
                                                                    =
                                                                    let uu____4047
                                                                    =
                                                                    let uu____4057
                                                                    =
                                                                    let uu____4058
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4058
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____4057,
                                                                    "Print SMT query statistics")
                                                                     in
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
                                                                    "record_hints",
                                                                    uu____4082,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____4085
                                                                    =
                                                                    let uu____4097
                                                                    =
                                                                    let uu____4109
                                                                    =
                                                                    let uu____4119
                                                                    =
                                                                    let uu____4120
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4120
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4119,
                                                                    " ")  in
                                                                    let uu____4122
                                                                    =
                                                                    let uu____4134
                                                                    =
                                                                    let uu____4146
                                                                    =
                                                                    let uu____4158
                                                                    =
                                                                    let uu____4170
                                                                    =
                                                                    let uu____4182
                                                                    =
                                                                    let uu____4192
                                                                    =
                                                                    let uu____4193
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4193
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4192,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4195
                                                                    =
                                                                    let uu____4207
                                                                    =
                                                                    let uu____4217
                                                                    =
                                                                    let uu____4218
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4218
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4217,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4220
                                                                    =
                                                                    let uu____4232
                                                                    =
                                                                    let uu____4244
                                                                    =
                                                                    let uu____4254
                                                                    =
                                                                    let uu____4255
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4255
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4254,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4257
                                                                    =
                                                                    let uu____4269
                                                                    =
                                                                    let uu____4279
                                                                    =
                                                                    let uu____4280
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4280
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4279,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4282
                                                                    =
                                                                    let uu____4294
                                                                    =
                                                                    let uu____4304
                                                                    =
                                                                    let uu____4305
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4305
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4304,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4307
                                                                    =
                                                                    let uu____4319
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
                                                                    "unthrottle_inductives",
                                                                    uu____4329,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4332
                                                                    =
                                                                    let uu____4344
                                                                    =
                                                                    let uu____4354
                                                                    =
                                                                    let uu____4355
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4355
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4354,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4357
                                                                    =
                                                                    let uu____4369
                                                                    =
                                                                    let uu____4379
                                                                    =
                                                                    let uu____4380
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4380
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4379,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4382
                                                                    =
                                                                    let uu____4394
                                                                    =
                                                                    let uu____4404
                                                                    =
                                                                    let uu____4405
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4405
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4404,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4407
                                                                    =
                                                                    let uu____4419
                                                                    =
                                                                    let uu____4429
                                                                    =
                                                                    let uu____4430
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4430
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4429,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4432
                                                                    =
                                                                    let uu____4444
                                                                    =
                                                                    let uu____4456
                                                                    =
                                                                    let uu____4466
                                                                    =
                                                                    let uu____4467
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4467
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4466,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4469
                                                                    =
                                                                    let uu____4481
                                                                    =
                                                                    let uu____4493
                                                                    =
                                                                    let uu____4505
                                                                    =
                                                                    let uu____4517
                                                                    =
                                                                    let uu____4527
                                                                    =
                                                                    let uu____4528
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4528
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4527,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4530
                                                                    =
                                                                    let uu____4542
                                                                    =
                                                                    let uu____4552
                                                                    =
                                                                    let uu____4553
                                                                    =
                                                                    let uu____4561
                                                                    =
                                                                    let uu____4562
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4562
                                                                     in
                                                                    ((fun
                                                                    uu____4568
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4561)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4553
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4552,
                                                                    "Display version number")
                                                                     in
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
                                                                    "warn_default_effects",
                                                                    uu____4594,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4597
                                                                    =
                                                                    let uu____4609
                                                                    =
                                                                    let uu____4621
                                                                    =
                                                                    let uu____4631
                                                                    =
                                                                    let uu____4632
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4632
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4631,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4634
                                                                    =
                                                                    let uu____4646
                                                                    =
                                                                    let uu____4658
                                                                    =
                                                                    let uu____4670
                                                                    =
                                                                    let uu____4682
                                                                    =
                                                                    let uu____4694
                                                                    =
                                                                    let uu____4704
                                                                    =
                                                                    let uu____4705
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4705
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4704,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4707
                                                                    =
                                                                    let uu____4719
                                                                    =
                                                                    let uu____4729
                                                                    =
                                                                    let uu____4730
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4730
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4729,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4732
                                                                    =
                                                                    let uu____4744
                                                                    =
                                                                    let uu____4756
                                                                    =
                                                                    let uu____4768
                                                                    =
                                                                    let uu____4778
                                                                    =
                                                                    let uu____4779
                                                                    =
                                                                    let uu____4787
                                                                    =
                                                                    let uu____4788
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4788
                                                                     in
                                                                    ((fun
                                                                    uu____4794
                                                                     ->
                                                                    (
                                                                    let uu____4796
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4796);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4787)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4779
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4778,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4768]
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4756
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4744
                                                                     in
                                                                    uu____4719
                                                                    ::
                                                                    uu____4732
                                                                     in
                                                                    uu____4694
                                                                    ::
                                                                    uu____4707
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4682
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4670
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4658
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4646
                                                                     in
                                                                    uu____4621
                                                                    ::
                                                                    uu____4634
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4609
                                                                     in
                                                                    uu____4584
                                                                    ::
                                                                    uu____4597
                                                                     in
                                                                    uu____4542
                                                                    ::
                                                                    uu____4572
                                                                     in
                                                                    uu____4517
                                                                    ::
                                                                    uu____4530
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4505
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4493
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4481
                                                                     in
                                                                    uu____4456
                                                                    ::
                                                                    uu____4469
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4444
                                                                     in
                                                                    uu____4419
                                                                    ::
                                                                    uu____4432
                                                                     in
                                                                    uu____4394
                                                                    ::
                                                                    uu____4407
                                                                     in
                                                                    uu____4369
                                                                    ::
                                                                    uu____4382
                                                                     in
                                                                    uu____4344
                                                                    ::
                                                                    uu____4357
                                                                     in
                                                                    uu____4319
                                                                    ::
                                                                    uu____4332
                                                                     in
                                                                    uu____4294
                                                                    ::
                                                                    uu____4307
                                                                     in
                                                                    uu____4269
                                                                    ::
                                                                    uu____4282
                                                                     in
                                                                    uu____4244
                                                                    ::
                                                                    uu____4257
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4232
                                                                     in
                                                                    uu____4207
                                                                    ::
                                                                    uu____4220
                                                                     in
                                                                    uu____4182
                                                                    ::
                                                                    uu____4195
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4170
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4158
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4146
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4134
                                                                     in
                                                                    uu____4109
                                                                    ::
                                                                    uu____4122
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____4097
                                                                     in
                                                                    uu____4072
                                                                    ::
                                                                    uu____4085
                                                                     in
                                                                    uu____4047
                                                                    ::
                                                                    uu____4060
                                                                     in
                                                                    uu____4022
                                                                    ::
                                                                    uu____4035
                                                                     in
                                                                    uu____3997
                                                                    ::
                                                                    uu____4010
                                                                     in
                                                                    uu____3972
                                                                    ::
                                                                    uu____3985
                                                                     in
                                                                    uu____3947
                                                                    ::
                                                                    uu____3960
                                                                     in
                                                                    uu____3922
                                                                    ::
                                                                    uu____3935
                                                                     in
                                                                    uu____3897
                                                                    ::
                                                                    uu____3910
                                                                     in
                                                                    uu____3872
                                                                    ::
                                                                    uu____3885
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3860
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3848
                                                                     in
                                                                    uu____3823
                                                                    ::
                                                                    uu____3836
                                                                     in
                                                                    uu____3798
                                                                    ::
                                                                    uu____3811
                                                                     in
                                                                    uu____3773
                                                                    ::
                                                                    uu____3786
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3761
                                                                     in
                                                                    uu____3736
                                                                    ::
                                                                    uu____3749
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3724
                                                                     in
                                                                    uu____3699
                                                                    ::
                                                                    uu____3712
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3687
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3675
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3663
                                                                     in
                                                                    uu____3638
                                                                    ::
                                                                    uu____3651
                                                                     in
                                                                    uu____3613
                                                                    ::
                                                                    uu____3626
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3601
                                                                     in
                                                                    uu____3576
                                                                    ::
                                                                    uu____3589
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (
                                                                    IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____3564
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_fuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of recursive functions to try initially (default 2)")
                                                                  ::
                                                                  uu____3552
                                                                 in
                                                              uu____3527 ::
                                                                uu____3540
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "include",
                                                              (ReverseAccumulated
                                                                 (PathStr
                                                                    "path")),
                                                              "A directory in which to search for files included on the command line")
                                                              :: uu____3515
                                                             in
                                                          uu____3490 ::
                                                            uu____3503
                                                           in
                                                        uu____3465 ::
                                                          uu____3478
                                                         in
                                                      uu____3440 ::
                                                        uu____3453
                                                       in
                                                    (FStar_Getopt.noshort,
                                                      "hint_file",
                                                      (PathStr "path"),
                                                      "Read/write hints to <path> (instead of module-specific hints files)")
                                                      :: uu____3428
                                                     in
                                                  uu____3403 :: uu____3416
                                                   in
                                                uu____3378 :: uu____3391  in
                                              (FStar_Getopt.noshort,
                                                "extract_namespace",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "namespace name")))),
                                                "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                :: uu____3366
                                               in
                                            (FStar_Getopt.noshort,
                                              "extract_module",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "module_name")))),
                                              "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                              :: uu____3354
                                             in
                                          (FStar_Getopt.noshort, "extract",
                                            (Accumulated
                                               (SimpleStr
                                                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                            "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                            :: uu____3342
                                           in
                                        uu____3317 :: uu____3330  in
                                      uu____3292 :: uu____3305  in
                                    uu____3267 :: uu____3280  in
                                  (FStar_Getopt.noshort, "dump_module",
                                    (Accumulated (SimpleStr "module_name")),
                                    "") :: uu____3255
                                   in
                                uu____3230 :: uu____3243  in
                              uu____3205 :: uu____3218  in
                            uu____3180 :: uu____3193  in
                          (FStar_Getopt.noshort, "dep",
                            (EnumStr ["make"; "graph"; "full"]),
                            "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                            :: uu____3168
                           in
                        (FStar_Getopt.noshort, "defensive",
                          (EnumStr ["no"; "warn"; "fail"]),
                          "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                          :: uu____3156
                         in
                      (FStar_Getopt.noshort, "debug_level",
                        (Accumulated
                           (OpenEnumStr
                              (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                        "Control the verbosity of debugging info") ::
                        uu____3144
                       in
                    (FStar_Getopt.noshort, "debug",
                      (Accumulated (SimpleStr "module_name")),
                      "Print lots of debugging information while checking module")
                      :: uu____3132
                     in
                  (FStar_Getopt.noshort, "codegen-lib",
                    (Accumulated (SimpleStr "namespace")),
                    "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                    :: uu____3120
                   in
                (FStar_Getopt.noshort, "codegen",
                  (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                  "Generate code for further compilation to executable code, or build a compiler plugin")
                  :: uu____3108
                 in
              uu____3083 :: uu____3096  in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____3071
             in
          uu____3046 :: uu____3059  in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____3034
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____3022
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___82_5722  ->
             match uu___82_5722 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____3010

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5749  ->
    let uu____5752 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5779  ->
         match uu____5779 with
         | (short,long,typ,doc) ->
             let uu____5795 =
               let uu____5807 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5807, doc)  in
             mk_spec uu____5795) uu____5752

let (settable : Prims.string -> Prims.bool) =
  fun uu___83_5817  ->
    match uu___83_5817 with
    | "abort_on" -> true
    | "admit_smt_queries" -> true
    | "admit_except" -> true
    | "debug" -> true
    | "debug_level" -> true
    | "defensive" -> true
    | "detail_errors" -> true
    | "detail_hint_replay" -> true
    | "eager_embedding" -> true
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
    | uu____5818 -> false
  
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
       (fun uu____5892  ->
          match uu____5892 with
          | (uu____5904,x,uu____5906,uu____5907) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____5969  ->
          match uu____5969 with
          | (uu____5981,x,uu____5983,uu____5984) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____5995  ->
    let uu____5996 = specs ()  in display_usage_aux uu____5996
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____6020 -> true
    | uu____6021 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____6028 -> uu____6028
  
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
          let uu____6056 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____6056
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____6084  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____6089 =
             let uu____6092 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____6092 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____6089)
       in
    let uu____6149 =
      let uu____6152 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6152
       in
    (res, uu____6149)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6190  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6229 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6229 (fun x  -> ())  in
     (let uu____6235 =
        let uu____6240 =
          let uu____6241 = FStar_List.map mk_string old_verify_module  in
          List uu____6241  in
        ("verify_module", uu____6240)  in
      set_option' uu____6235);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6251 =
        let uu____6252 =
          let uu____6253 =
            let uu____6254 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6254  in
          (FStar_String.length f1) - uu____6253  in
        uu____6252 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6251  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6260 = get_lax ()  in
    if uu____6260
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6270 = module_name_of_file_name fn  in should_verify uu____6270
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6276 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6276
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6284 = should_verify m  in
    if uu____6284 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6292  ->
    let uu____6293 = get_no_default_includes ()  in
    if uu____6293
    then get_include ()
    else
      (let lib_paths =
         let uu____6300 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6300 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6309 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6309
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6323 =
         let uu____6326 = get_include ()  in
         FStar_List.append uu____6326 ["."]  in
       FStar_List.append lib_paths uu____6323)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____6339 = FStar_Util.smap_try_find file_map filename  in
    match uu____6339 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            let uu____6355 = FStar_Util.is_path_absolute filename  in
            if uu____6355
            then
              (if FStar_Util.file_exists filename
               then FStar_Pervasives_Native.Some filename
               else FStar_Pervasives_Native.None)
            else
              (let uu____6362 =
                 let uu____6365 = include_path ()  in
                 FStar_List.rev uu____6365  in
               FStar_Util.find_map uu____6362
                 (fun p  ->
                    let path =
                      if p = "."
                      then filename
                      else FStar_Util.join_paths p filename  in
                    if FStar_Util.file_exists path
                    then FStar_Pervasives_Native.Some path
                    else FStar_Pervasives_Native.None))
          with | uu____6381 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____6390  ->
    let uu____6391 = get_prims ()  in
    match uu____6391 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6395 = find_file filename  in
        (match uu____6395 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6399 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6399)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6405  ->
    let uu____6406 = prims ()  in FStar_Util.basename uu____6406
  
let (pervasives : unit -> Prims.string) =
  fun uu____6411  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____6413 = find_file filename  in
    match uu____6413 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____6417 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6417
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6422  ->
    let uu____6423 = pervasives ()  in FStar_Util.basename uu____6423
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6428  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____6430 = find_file filename  in
    match uu____6430 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____6434 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6434
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____6440 = get_odir ()  in
    match uu____6440 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____6449 = get_cache_dir ()  in
    match uu____6449 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6453 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____6453
  
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
             let uu____6519 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____6519  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____6527 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6527 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6597 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6597 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6606  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6611  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6618  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6623  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____6628  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6634 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6640 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6646 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6652 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6659  ->
    let uu____6660 = get_codegen ()  in
    FStar_Util.map_opt uu____6660
      (fun uu___84_6664  ->
         match uu___84_6664 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6665 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6674  ->
    let uu____6675 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6675
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6692  -> let uu____6693 = get_debug ()  in uu____6693 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6703 = get_debug ()  in
    FStar_All.pipe_right uu____6703 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6720 = get_debug ()  in
       FStar_All.pipe_right uu____6720 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6729  -> let uu____6730 = get_defensive ()  in uu____6730 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6735  ->
    let uu____6736 = get_defensive ()  in uu____6736 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6743  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6748  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6753  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6758  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6764 = get_dump_module ()  in
    FStar_All.pipe_right uu____6764 (FStar_List.contains s)
  
let (eager_embedding : unit -> Prims.bool) =
  fun uu____6773  -> get_eager_embedding () 
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6778  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6783  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6789 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6789
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6823  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6828  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6833  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6840  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6845  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6850  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____6855  ->
    let uu____6856 = get_initial_fuel ()  in
    let uu____6857 = get_max_fuel ()  in Prims.min uu____6856 uu____6857
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____6862  ->
    let uu____6863 = get_initial_ifuel ()  in
    let uu____6864 = get_max_ifuel ()  in Prims.min uu____6863 uu____6864
  
let (interactive : unit -> Prims.bool) =
  fun uu____6869  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____6874  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____6881  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____6886  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____6891  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____6896  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____6901  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____6906  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____6911  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____6916  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____6921  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____6926  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____6931  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____6938 = get_no_extract ()  in
    FStar_All.pipe_right uu____6938
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____6949  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____6954  -> get_no_location_info () 
let (no_smt : unit -> Prims.bool) = fun uu____6959  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6966  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____6971  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____6976  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____6981  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____6986  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____6991  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____6996  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____7001  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____7006  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____7011  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7018  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____7023  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____7028  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____7033  ->
    let uu____7034 = get_smtencoding_nl_arith_repr ()  in
    uu____7034 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____7039  ->
    let uu____7040 = get_smtencoding_nl_arith_repr ()  in
    uu____7040 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____7045  ->
    let uu____7046 = get_smtencoding_nl_arith_repr ()  in
    uu____7046 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____7051  ->
    let uu____7052 = get_smtencoding_l_arith_repr ()  in
    uu____7052 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____7057  ->
    let uu____7058 = get_smtencoding_l_arith_repr ()  in
    uu____7058 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____7063  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____7068  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____7073  -> get_tactic_trace_d () 
let (timing : unit -> Prims.bool) = fun uu____7078  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____7083  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____7088  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____7093  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____7098  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____7103  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____7108  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7115  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____7120  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____7133  ->
    let uu____7134 = get_using_facts_from ()  in
    match uu____7134 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7172  ->
    let uu____7173 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____7173
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7180  ->
    let uu____7181 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____7181 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7184 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7191  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____7196  ->
    let uu____7197 = get_smt ()  in
    match uu____7197 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7207  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____7212  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____7217  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7222  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____7227  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7232  ->
    (get_use_two_phase_tc ()) &&
      (let uu____7234 = lax ()  in Prims.op_Negation uu____7234)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7239  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7244  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7249  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7254  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7261 = get_extract ()  in
    match uu____7261 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7272 =
            let uu____7285 = get_no_extract ()  in
            let uu____7288 = get_extract_namespace ()  in
            let uu____7291 = get_extract_module ()  in
            (uu____7285, uu____7288, uu____7291)  in
          match uu____7272 with
          | ([],[],[]) -> ()
          | uu____7306 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7354,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7373 -> false  in
          let uu____7382 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7416  ->
                    match uu____7416 with
                    | (path,uu____7424) -> matches_path m_components path))
             in
          match uu____7382 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____7435,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____7455 = get_extract_namespace ()  in
          match uu____7455 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____7471 = get_extract_module ()  in
          match uu____7471 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____7483 = no_extract m1  in Prims.op_Negation uu____7483) &&
          (let uu____7485 =
             let uu____7494 = get_extract_namespace ()  in
             let uu____7497 = get_extract_module ()  in
             (uu____7494, uu____7497)  in
           (match uu____7485 with
            | ([],[]) -> true
            | uu____7508 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  