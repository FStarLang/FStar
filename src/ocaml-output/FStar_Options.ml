open Prims
let (debug_embedding : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (eager_embedding : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
type debug_level_t =
  | Low 
  | Medium 
  | High 
  | Extreme 
  | Other of Prims.string 
let (uu___is_Low : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | Low  -> true | uu____59 -> false 
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____65 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | High  -> true | uu____71 -> false 
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____77 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____84 -> false
  
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
    match projectee with | Bool _0 -> true | uu____125 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____139 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____153 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____167 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____183 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____202 -> false
  
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
  fun projectee  -> match projectee with | Set  -> true | uu____230 -> false 
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____236 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____242 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____260  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____284  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____308  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___76_332  ->
    match uu___76_332 with
    | Bool b -> b
    | uu____334 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___77_339  ->
    match uu___77_339 with
    | Int b -> b
    | uu____341 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___78_346  ->
    match uu___78_346 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____349 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___79_356  ->
    match uu___79_356 with
    | List ts -> ts
    | uu____362 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____371 .
    (option_val -> 'Auu____371) -> option_val -> 'Auu____371 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____389 = as_list' x  in
      FStar_All.pipe_right uu____389 (FStar_List.map as_t)
  
let as_option :
  'Auu____402 .
    (option_val -> 'Auu____402) ->
      option_val -> 'Auu____402 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___80_417  ->
      match uu___80_417 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____421 = as_t v1  in FStar_Pervasives_Native.Some uu____421
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___81_428  ->
    match uu___81_428 with
    | List ls ->
        let uu____434 =
          FStar_List.map
            (fun l  ->
               let uu____444 = as_string l  in FStar_Util.split uu____444 ",")
            ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____434
    | uu____451 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let (fstar_options : optionstate Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : unit -> optionstate) =
  fun uu____477  ->
    let uu____478 = FStar_ST.op_Bang fstar_options  in
    FStar_List.hd uu____478
  
let (pop : unit -> unit) =
  fun uu____508  ->
    let uu____509 = FStar_ST.op_Bang fstar_options  in
    match uu____509 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____535::[] -> failwith "TOO MANY POPS!"
    | uu____536::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____567  ->
    let uu____568 =
      let uu____571 =
        let uu____572 = peek ()  in FStar_Util.smap_copy uu____572  in
      let uu____575 = FStar_ST.op_Bang fstar_options  in uu____571 ::
        uu____575
       in
    FStar_ST.op_Colon_Equals fstar_options uu____568
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____629 = FStar_ST.op_Bang fstar_options  in
    match uu____629 with
    | [] -> failwith "set on empty option stack"
    | uu____655::os -> FStar_ST.op_Colon_Equals fstar_options (o :: os)
  
let (snapshot : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____690  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  -> let uu____710 = peek ()  in FStar_Util.smap_add uu____710 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____721  -> match uu____721 with | (k,v1) -> set_option k v1 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  -> push (); (let retv = f ()  in pop (); retv) 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____768 =
      let uu____771 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____771
       in
    FStar_ST.op_Colon_Equals light_off_files uu____768
  
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
  ("no_plugins", (Bool false));
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
  ("tcnorm", (Bool true));
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
  ("__tactics_nbe", (Bool false));
  ("warn_error", (String ""));
  ("use_extracted_interfaces", (Bool false))] 
let (init : unit -> unit) =
  fun uu____1230  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1247  ->
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
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1450  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1455  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1464  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1477  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1486  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1493  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1498  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1503  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1510  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1517  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1522  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1529  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1536  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1541  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1546  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1551  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1558  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1565  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1570  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1575  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1580  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1585  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1590  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1595  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1600  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1607  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1614  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____1619  -> lookup_opt "no_plugins" as_bool 
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
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____1755  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____1760  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____1765  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____1770  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____1775  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____1780  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____1785  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____1790  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____1795  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1802  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____1809  ->
    let uu____1810 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____1810
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1819  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1832  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____1841  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____1850  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____1857  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____1862  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____1869  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____1876  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____1881  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____1886  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____1891  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____1896  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____1901  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____1906  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____1911  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____1916  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___82_1921  ->
    match uu___82_1921 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____1933 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____1939 = get_debug_level ()  in
    FStar_All.pipe_right uu____1939
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2072  ->
    let uu____2073 =
      let uu____2074 = FStar_ST.op_Bang _version  in
      let uu____2094 = FStar_ST.op_Bang _platform  in
      let uu____2114 = FStar_ST.op_Bang _compiler  in
      let uu____2134 = FStar_ST.op_Bang _date  in
      let uu____2154 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2074
        uu____2094 uu____2114 uu____2134 uu____2154
       in
    FStar_Util.print_string uu____2073
  
let display_usage_aux :
  'Auu____2180 'Auu____2181 .
    ('Auu____2180,Prims.string,'Auu____2181 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2229  ->
         match uu____2229 with
         | (uu____2240,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2252 =
                      let uu____2253 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2253  in
                    FStar_Util.print_string uu____2252
                  else
                    (let uu____2255 =
                       let uu____2256 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2256 doc  in
                     FStar_Util.print_string uu____2255)
              | FStar_Getopt.OneArg (uu____2257,argname) ->
                  if doc = ""
                  then
                    let uu____2265 =
                      let uu____2266 = FStar_Util.colorize_bold flag  in
                      let uu____2267 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2266 uu____2267
                       in
                    FStar_Util.print_string uu____2265
                  else
                    (let uu____2269 =
                       let uu____2270 = FStar_Util.colorize_bold flag  in
                       let uu____2271 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2270
                         uu____2271 doc
                        in
                     FStar_Util.print_string uu____2269))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2299 = o  in
    match uu____2299 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2335 =
                let uu____2336 = f ()  in set_option name uu____2336  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2351 = f x  in set_option name uu____2351
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2371 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2371  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2394 =
        let uu____2397 = lookup_opt name as_list'  in
        FStar_List.append uu____2397 [value]  in
      mk_list uu____2394
  
let accumulate_string :
  'Auu____2410 .
    Prims.string -> ('Auu____2410 -> Prims.string) -> 'Auu____2410 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2431 =
          let uu____2432 =
            let uu____2433 = post_processor value  in mk_string uu____2433
             in
          accumulated_option name uu____2432  in
        set_option name uu____2431
  
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
    match projectee with | Const _0 -> true | uu____2529 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2543 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2556 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2563 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2577 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2593 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2619 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____2658 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____2693 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____2707 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____2728 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____2766 -> true
    | uu____2767 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____2774 -> uu____2774
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___87_2792  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____2794 ->
                      let uu____2795 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____2795 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____2799 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____2799
                  | PathStr uu____2802 -> mk_path str_val
                  | SimpleStr uu____2803 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____2808 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____2823 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____2823
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
            let uu____2842 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____2842
  
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
    | PostProcessed (uu____2879,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____2889,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____2916 = desc_of_opt_type typ  in
      match uu____2916 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____2922  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____2939 =
      let uu____2940 = as_string s  in FStar_String.lowercase uu____2940  in
    mk_string uu____2939
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____2988  ->
    let uu____3000 =
      let uu____3012 =
        let uu____3024 =
          let uu____3036 =
            let uu____3046 =
              let uu____3047 = mk_bool true  in Const uu____3047  in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____3046,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
             in
          let uu____3049 =
            let uu____3061 =
              let uu____3073 =
                let uu____3083 =
                  let uu____3084 = mk_bool true  in Const uu____3084  in
                (FStar_Getopt.noshort, "cache_off", uu____3083,
                  "Do not read or write any .checked files")
                 in
              let uu____3086 =
                let uu____3098 =
                  let uu____3110 =
                    let uu____3122 =
                      let uu____3134 =
                        let uu____3146 =
                          let uu____3158 =
                            let uu____3170 =
                              let uu____3180 =
                                let uu____3181 = mk_bool true  in
                                Const uu____3181  in
                              (FStar_Getopt.noshort, "detail_errors",
                                uu____3180,
                                "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                               in
                            let uu____3183 =
                              let uu____3195 =
                                let uu____3205 =
                                  let uu____3206 = mk_bool true  in
                                  Const uu____3206  in
                                (FStar_Getopt.noshort, "detail_hint_replay",
                                  uu____3205,
                                  "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                 in
                              let uu____3208 =
                                let uu____3220 =
                                  let uu____3230 =
                                    let uu____3231 = mk_bool true  in
                                    Const uu____3231  in
                                  (FStar_Getopt.noshort, "doc", uu____3230,
                                    "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                   in
                                let uu____3233 =
                                  let uu____3245 =
                                    let uu____3257 =
                                      let uu____3267 =
                                        let uu____3268 = mk_bool true  in
                                        Const uu____3268  in
                                      (FStar_Getopt.noshort,
                                        "eager_inference", uu____3267,
                                        "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                       in
                                    let uu____3270 =
                                      let uu____3282 =
                                        let uu____3292 =
                                          let uu____3293 = mk_bool true  in
                                          Const uu____3293  in
                                        (FStar_Getopt.noshort,
                                          "eager_subtyping", uu____3292,
                                          "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                         in
                                      let uu____3295 =
                                        let uu____3307 =
                                          let uu____3319 =
                                            let uu____3331 =
                                              let uu____3343 =
                                                let uu____3353 =
                                                  let uu____3354 =
                                                    mk_bool true  in
                                                  Const uu____3354  in
                                                (FStar_Getopt.noshort,
                                                  "expose_interfaces",
                                                  uu____3353,
                                                  "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                 in
                                              let uu____3356 =
                                                let uu____3368 =
                                                  let uu____3378 =
                                                    let uu____3379 =
                                                      mk_bool true  in
                                                    Const uu____3379  in
                                                  (FStar_Getopt.noshort,
                                                    "hide_uvar_nums",
                                                    uu____3378,
                                                    "Don't print unification variable numbers")
                                                   in
                                                let uu____3381 =
                                                  let uu____3393 =
                                                    let uu____3405 =
                                                      let uu____3415 =
                                                        let uu____3416 =
                                                          mk_bool true  in
                                                        Const uu____3416  in
                                                      (FStar_Getopt.noshort,
                                                        "hint_info",
                                                        uu____3415,
                                                        "Print information regarding hints (deprecated; use --query_stats instead)")
                                                       in
                                                    let uu____3418 =
                                                      let uu____3430 =
                                                        let uu____3440 =
                                                          let uu____3441 =
                                                            mk_bool true  in
                                                          Const uu____3441
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "in", uu____3440,
                                                          "Legacy interactive mode; reads input from stdin")
                                                         in
                                                      let uu____3443 =
                                                        let uu____3455 =
                                                          let uu____3465 =
                                                            let uu____3466 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3466
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "ide",
                                                            uu____3465,
                                                            "JSON-based interactive mode for IDEs")
                                                           in
                                                        let uu____3468 =
                                                          let uu____3480 =
                                                            let uu____3492 =
                                                              let uu____3502
                                                                =
                                                                let uu____3503
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____3503
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "indent",
                                                                uu____3502,
                                                                "Parses and outputs the files on the command line")
                                                               in
                                                            let uu____3505 =
                                                              let uu____3517
                                                                =
                                                                let uu____3529
                                                                  =
                                                                  let uu____3541
                                                                    =
                                                                    let uu____3551
                                                                    =
                                                                    let uu____3552
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3552
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3551,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                  let uu____3554
                                                                    =
                                                                    let uu____3566
                                                                    =
                                                                    let uu____3578
                                                                    =
                                                                    let uu____3588
                                                                    =
                                                                    let uu____3589
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3589
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3588,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3591
                                                                    =
                                                                    let uu____3603
                                                                    =
                                                                    let uu____3613
                                                                    =
                                                                    let uu____3614
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3614
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3613,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3616
                                                                    =
                                                                    let uu____3628
                                                                    =
                                                                    let uu____3640
                                                                    =
                                                                    let uu____3652
                                                                    =
                                                                    let uu____3664
                                                                    =
                                                                    let uu____3674
                                                                    =
                                                                    let uu____3675
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3675
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____3674,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____3677
                                                                    =
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
                                                                    "no_default_includes",
                                                                    uu____3711,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____3714
                                                                    =
                                                                    let uu____3726
                                                                    =
                                                                    let uu____3738
                                                                    =
                                                                    let uu____3748
                                                                    =
                                                                    let uu____3749
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3749
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____3748,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____3751
                                                                    =
                                                                    let uu____3763
                                                                    =
                                                                    let uu____3773
                                                                    =
                                                                    let uu____3774
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3774
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____3773,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____3776
                                                                    =
                                                                    let uu____3788
                                                                    =
                                                                    let uu____3798
                                                                    =
                                                                    let uu____3799
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3799
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____3798,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____3801
                                                                    =
                                                                    let uu____3813
                                                                    =
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
                                                                    "print_bound_var_types",
                                                                    uu____3847,
                                                                    "Print the types of bound variables")
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
                                                                    "print_effect_args",
                                                                    uu____3872,
                                                                    "Print inferred predicate transformers for all computation types")
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
                                                                    "print_full_names",
                                                                    uu____3897,
                                                                    "Print full names of variables")
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
                                                                    "print_implicits",
                                                                    uu____3922,
                                                                    "Print implicit arguments")
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
                                                                    "print_universes",
                                                                    uu____3947,
                                                                    "Print universes")
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
                                                                    "print_z3_statistics",
                                                                    uu____3972,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
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
                                                                    "prn",
                                                                    uu____3997,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____4000
                                                                    =
                                                                    let uu____4012
                                                                    =
                                                                    let uu____4022
                                                                    =
                                                                    let uu____4023
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4023
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____4022,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____4025
                                                                    =
                                                                    let uu____4037
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
                                                                    "record_hints",
                                                                    uu____4047,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____4050
                                                                    =
                                                                    let uu____4062
                                                                    =
                                                                    let uu____4074
                                                                    =
                                                                    let uu____4084
                                                                    =
                                                                    let uu____4085
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4085
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4084,
                                                                    " ")  in
                                                                    let uu____4087
                                                                    =
                                                                    let uu____4099
                                                                    =
                                                                    let uu____4111
                                                                    =
                                                                    let uu____4123
                                                                    =
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
                                                                    "tactic_raw_binders",
                                                                    uu____4157,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
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
                                                                    "tactic_trace",
                                                                    uu____4182,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4185
                                                                    =
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
                                                                    "__tactics_nbe",
                                                                    uu____4219,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____4222
                                                                    =
                                                                    let uu____4234
                                                                    =
                                                                    let uu____4246
                                                                    =
                                                                    let uu____4256
                                                                    =
                                                                    let uu____4257
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4257
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4256,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4259
                                                                    =
                                                                    let uu____4271
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
                                                                    "trace_error",
                                                                    uu____4281,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4284
                                                                    =
                                                                    let uu____4296
                                                                    =
                                                                    let uu____4306
                                                                    =
                                                                    let uu____4307
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4307
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4306,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4309
                                                                    =
                                                                    let uu____4321
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
                                                                    "unthrottle_inductives",
                                                                    uu____4331,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
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
                                                                    "unsafe_tactic_exec",
                                                                    uu____4356,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4359
                                                                    =
                                                                    let uu____4371
                                                                    =
                                                                    let uu____4381
                                                                    =
                                                                    let uu____4382
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4382
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4381,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4384
                                                                    =
                                                                    let uu____4396
                                                                    =
                                                                    let uu____4406
                                                                    =
                                                                    let uu____4407
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4407
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4406,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4409
                                                                    =
                                                                    let uu____4421
                                                                    =
                                                                    let uu____4431
                                                                    =
                                                                    let uu____4432
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4432
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4431,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4434
                                                                    =
                                                                    let uu____4446
                                                                    =
                                                                    let uu____4458
                                                                    =
                                                                    let uu____4468
                                                                    =
                                                                    let uu____4469
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4469
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____4468,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____4471
                                                                    =
                                                                    let uu____4483
                                                                    =
                                                                    let uu____4493
                                                                    =
                                                                    let uu____4494
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4494
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4493,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4496
                                                                    =
                                                                    let uu____4508
                                                                    =
                                                                    let uu____4520
                                                                    =
                                                                    let uu____4532
                                                                    =
                                                                    let uu____4544
                                                                    =
                                                                    let uu____4554
                                                                    =
                                                                    let uu____4555
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4555
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4554,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4557
                                                                    =
                                                                    let uu____4569
                                                                    =
                                                                    let uu____4579
                                                                    =
                                                                    let uu____4580
                                                                    =
                                                                    let uu____4588
                                                                    =
                                                                    let uu____4589
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4589
                                                                     in
                                                                    ((fun
                                                                    uu____4595
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4588)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4580
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4579,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____4599
                                                                    =
                                                                    let uu____4611
                                                                    =
                                                                    let uu____4621
                                                                    =
                                                                    let uu____4622
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4622
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____4621,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____4624
                                                                    =
                                                                    let uu____4636
                                                                    =
                                                                    let uu____4648
                                                                    =
                                                                    let uu____4658
                                                                    =
                                                                    let uu____4659
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4659
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____4658,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____4661
                                                                    =
                                                                    let uu____4673
                                                                    =
                                                                    let uu____4685
                                                                    =
                                                                    let uu____4697
                                                                    =
                                                                    let uu____4709
                                                                    =
                                                                    let uu____4721
                                                                    =
                                                                    let uu____4731
                                                                    =
                                                                    let uu____4732
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4732
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____4731,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____4734
                                                                    =
                                                                    let uu____4746
                                                                    =
                                                                    let uu____4756
                                                                    =
                                                                    let uu____4757
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4757
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____4756,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____4759
                                                                    =
                                                                    let uu____4771
                                                                    =
                                                                    let uu____4783
                                                                    =
                                                                    let uu____4795
                                                                    =
                                                                    let uu____4805
                                                                    =
                                                                    let uu____4806
                                                                    =
                                                                    let uu____4814
                                                                    =
                                                                    let uu____4815
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4815
                                                                     in
                                                                    ((fun
                                                                    uu____4820
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____4814)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4806
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____4805,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____4841
                                                                    =
                                                                    let uu____4853
                                                                    =
                                                                    let uu____4863
                                                                    =
                                                                    let uu____4864
                                                                    =
                                                                    let uu____4872
                                                                    =
                                                                    let uu____4873
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4873
                                                                     in
                                                                    ((fun
                                                                    uu____4878
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____4872)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4864
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____4863,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____4899
                                                                    =
                                                                    let uu____4911
                                                                    =
                                                                    let uu____4921
                                                                    =
                                                                    let uu____4922
                                                                    =
                                                                    let uu____4930
                                                                    =
                                                                    let uu____4931
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4931
                                                                     in
                                                                    ((fun
                                                                    uu____4937
                                                                     ->
                                                                    (
                                                                    let uu____4939
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____4939);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____4930)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4922
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____4921,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____4911]
                                                                     in
                                                                    uu____4853
                                                                    ::
                                                                    uu____4899
                                                                     in
                                                                    uu____4795
                                                                    ::
                                                                    uu____4841
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____4783
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____4771
                                                                     in
                                                                    uu____4746
                                                                    ::
                                                                    uu____4759
                                                                     in
                                                                    uu____4721
                                                                    ::
                                                                    uu____4734
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____4709
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____4697
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____4685
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____4673
                                                                     in
                                                                    uu____4648
                                                                    ::
                                                                    uu____4661
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____4636
                                                                     in
                                                                    uu____4611
                                                                    ::
                                                                    uu____4624
                                                                     in
                                                                    uu____4569
                                                                    ::
                                                                    uu____4599
                                                                     in
                                                                    uu____4544
                                                                    ::
                                                                    uu____4557
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4532
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4520
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4508
                                                                     in
                                                                    uu____4483
                                                                    ::
                                                                    uu____4496
                                                                     in
                                                                    uu____4458
                                                                    ::
                                                                    uu____4471
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4446
                                                                     in
                                                                    uu____4421
                                                                    ::
                                                                    uu____4434
                                                                     in
                                                                    uu____4396
                                                                    ::
                                                                    uu____4409
                                                                     in
                                                                    uu____4371
                                                                    ::
                                                                    uu____4384
                                                                     in
                                                                    uu____4346
                                                                    ::
                                                                    uu____4359
                                                                     in
                                                                    uu____4321
                                                                    ::
                                                                    uu____4334
                                                                     in
                                                                    uu____4296
                                                                    ::
                                                                    uu____4309
                                                                     in
                                                                    uu____4271
                                                                    ::
                                                                    uu____4284
                                                                     in
                                                                    uu____4246
                                                                    ::
                                                                    uu____4259
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____4234
                                                                     in
                                                                    uu____4209
                                                                    ::
                                                                    uu____4222
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4197
                                                                     in
                                                                    uu____4172
                                                                    ::
                                                                    uu____4185
                                                                     in
                                                                    uu____4147
                                                                    ::
                                                                    uu____4160
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4135
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4123
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4111
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4099
                                                                     in
                                                                    uu____4074
                                                                    ::
                                                                    uu____4087
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____4062
                                                                     in
                                                                    uu____4037
                                                                    ::
                                                                    uu____4050
                                                                     in
                                                                    uu____4012
                                                                    ::
                                                                    uu____4025
                                                                     in
                                                                    uu____3987
                                                                    ::
                                                                    uu____4000
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
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____3825
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____3813
                                                                     in
                                                                    uu____3788
                                                                    ::
                                                                    uu____3801
                                                                     in
                                                                    uu____3763
                                                                    ::
                                                                    uu____3776
                                                                     in
                                                                    uu____3738
                                                                    ::
                                                                    uu____3751
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____3726
                                                                     in
                                                                    uu____3701
                                                                    ::
                                                                    uu____3714
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____3689
                                                                     in
                                                                    uu____3664
                                                                    ::
                                                                    uu____3677
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____3652
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____3640
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3628
                                                                     in
                                                                    uu____3603
                                                                    ::
                                                                    uu____3616
                                                                     in
                                                                    uu____3578
                                                                    ::
                                                                    uu____3591
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3566
                                                                     in
                                                                  uu____3541
                                                                    ::
                                                                    uu____3554
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_ifuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                  ::
                                                                  uu____3529
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_fuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of recursive functions to try initially (default 2)")
                                                                :: uu____3517
                                                               in
                                                            uu____3492 ::
                                                              uu____3505
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "include",
                                                            (ReverseAccumulated
                                                               (PathStr
                                                                  "path")),
                                                            "A directory in which to search for files included on the command line")
                                                            :: uu____3480
                                                           in
                                                        uu____3455 ::
                                                          uu____3468
                                                         in
                                                      uu____3430 ::
                                                        uu____3443
                                                       in
                                                    uu____3405 :: uu____3418
                                                     in
                                                  (FStar_Getopt.noshort,
                                                    "hint_file",
                                                    (PathStr "path"),
                                                    "Read/write hints to <path> (instead of module-specific hints files)")
                                                    :: uu____3393
                                                   in
                                                uu____3368 :: uu____3381  in
                                              uu____3343 :: uu____3356  in
                                            (FStar_Getopt.noshort,
                                              "extract_namespace",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "namespace name")))),
                                              "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                              :: uu____3331
                                             in
                                          (FStar_Getopt.noshort,
                                            "extract_module",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr "module_name")))),
                                            "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                            :: uu____3319
                                           in
                                        (FStar_Getopt.noshort, "extract",
                                          (Accumulated
                                             (SimpleStr
                                                "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                          "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                          :: uu____3307
                                         in
                                      uu____3282 :: uu____3295  in
                                    uu____3257 :: uu____3270  in
                                  (FStar_Getopt.noshort, "dump_module",
                                    (Accumulated (SimpleStr "module_name")),
                                    "") :: uu____3245
                                   in
                                uu____3220 :: uu____3233  in
                              uu____3195 :: uu____3208  in
                            uu____3170 :: uu____3183  in
                          (FStar_Getopt.noshort, "dep",
                            (EnumStr ["make"; "graph"; "full"]),
                            "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                            :: uu____3158
                           in
                        (FStar_Getopt.noshort, "defensive",
                          (EnumStr ["no"; "warn"; "fail"]),
                          "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                          :: uu____3146
                         in
                      (FStar_Getopt.noshort, "debug_level",
                        (Accumulated
                           (OpenEnumStr
                              (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                        "Control the verbosity of debugging info") ::
                        uu____3134
                       in
                    (FStar_Getopt.noshort, "debug",
                      (Accumulated (SimpleStr "module_name")),
                      "Print lots of debugging information while checking module")
                      :: uu____3122
                     in
                  (FStar_Getopt.noshort, "codegen-lib",
                    (Accumulated (SimpleStr "namespace")),
                    "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                    :: uu____3110
                   in
                (FStar_Getopt.noshort, "codegen",
                  (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                  "Generate code for further compilation to executable code, or build a compiler plugin")
                  :: uu____3098
                 in
              uu____3073 :: uu____3086  in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____3061
             in
          uu____3036 :: uu____3049  in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____3024
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____3012
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___83_5902  ->
             match uu___83_5902 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____3000

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____5925  ->
    let uu____5928 = specs_with_types ()  in
    FStar_List.map
      (fun uu____5955  ->
         match uu____5955 with
         | (short,long,typ,doc) ->
             let uu____5971 =
               let uu____5983 = arg_spec_of_opt_type long typ  in
               (short, long, uu____5983, doc)  in
             mk_spec uu____5971) uu____5928

let (settable : Prims.string -> Prims.bool) =
  fun uu___84_5993  ->
    match uu___84_5993 with
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
    | "no_plugins" -> true
    | "no_tactics" -> true
    | "normalize_pure_terms_for_extraction" -> true
    | "tactic_raw_binders" -> true
    | "tactic_trace" -> true
    | "tactic_trace_d" -> true
    | "tcnorm" -> true
    | "__tactics_nbe" -> true
    | "__temp_fast_implicits" -> true
    | "__temp_no_proj" -> true
    | "reuse_hint_for" -> true
    | "warn_error" -> true
    | "z3rlimit_factor" -> true
    | "z3rlimit" -> true
    | "z3refresh" -> true
    | "use_two_phase_tc" -> true
    | "vcgen.optimize_bind_as_seq" -> true
    | uu____5994 -> false
  
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
       (fun uu____6068  ->
          match uu____6068 with
          | (uu____6080,x,uu____6082,uu____6083) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____6145  ->
          match uu____6145 with
          | (uu____6157,x,uu____6159,uu____6160) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____6171  ->
    let uu____6172 = specs ()  in display_usage_aux uu____6172
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____6196 -> true
    | uu____6197 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____6204 -> uu____6204
  
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
        (fun uu___89_6221  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____6232 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____6232
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____6260  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____6265 =
             let uu____6268 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____6268 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____6265)
       in
    let uu____6317 =
      let uu____6320 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6320
       in
    (res, uu____6317)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6354  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6389 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6389 (fun x  -> ())  in
     (let uu____6395 =
        let uu____6400 =
          let uu____6401 = FStar_List.map mk_string old_verify_module  in
          List uu____6401  in
        ("verify_module", uu____6400)  in
      set_option' uu____6395);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6411 =
        let uu____6412 =
          let uu____6413 =
            let uu____6414 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6414  in
          (FStar_String.length f1) - uu____6413  in
        uu____6412 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6411  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6420 = get_lax ()  in
    if uu____6420
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6430 = module_name_of_file_name fn  in should_verify uu____6430
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6436 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6436
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6444 = should_verify m  in
    if uu____6444 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6452  ->
    let uu____6453 = get_no_default_includes ()  in
    if uu____6453
    then get_include ()
    else
      (let lib_paths =
         let uu____6460 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6460 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6469 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6469
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6483 =
         let uu____6486 = get_include ()  in
         FStar_List.append uu____6486 ["."]  in
       FStar_List.append lib_paths uu____6483)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____6499 = FStar_Util.smap_try_find file_map filename  in
    match uu____6499 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___91_6512  ->
               match () with
               | () ->
                   let uu____6515 = FStar_Util.is_path_absolute filename  in
                   if uu____6515
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____6522 =
                        let uu____6525 = include_path ()  in
                        FStar_List.rev uu____6525  in
                      FStar_Util.find_map uu____6522
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___90_6537 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____6548  ->
    let uu____6549 = get_prims ()  in
    match uu____6549 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6553 = find_file filename  in
        (match uu____6553 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6557 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6557)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6563  ->
    let uu____6564 = prims ()  in FStar_Util.basename uu____6564
  
let (pervasives : unit -> Prims.string) =
  fun uu____6569  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____6571 = find_file filename  in
    match uu____6571 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____6575 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6575
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____6580  ->
    let uu____6581 = pervasives ()  in FStar_Util.basename uu____6581
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____6586  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____6588 = find_file filename  in
    match uu____6588 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____6592 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____6592
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____6598 = get_odir ()  in
    match uu____6598 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____6607 = get_cache_dir ()  in
    match uu____6607 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____6611 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____6611
  
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
             let uu____6677 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____6677  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____6685 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____6685 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6755 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____6755 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____6764  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____6769  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6776  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____6781  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____6786  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____6792 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____6798 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____6804 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____6810 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____6817  ->
    let uu____6818 = get_codegen ()  in
    FStar_Util.map_opt uu____6818
      (fun uu___85_6822  ->
         match uu___85_6822 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____6823 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____6832  ->
    let uu____6833 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____6833
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____6850  -> let uu____6851 = get_debug ()  in uu____6851 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____6861 = get_debug ()  in
    FStar_All.pipe_right uu____6861 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____6878 = get_debug ()  in
       FStar_All.pipe_right uu____6878 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____6887  -> let uu____6888 = get_defensive ()  in uu____6888 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____6893  ->
    let uu____6894 = get_defensive ()  in uu____6894 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6901  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____6906  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____6911  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____6916  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____6922 = get_dump_module ()  in
    FStar_All.pipe_right uu____6922 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____6931  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____6936  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____6942 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____6942
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____6972  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____6977  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____6982  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____6989  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____6994  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____6999  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____7004  ->
    let uu____7005 = get_initial_fuel ()  in
    let uu____7006 = get_max_fuel ()  in Prims.min uu____7005 uu____7006
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____7011  ->
    let uu____7012 = get_initial_ifuel ()  in
    let uu____7013 = get_max_ifuel ()  in Prims.min uu____7012 uu____7013
  
let (interactive : unit -> Prims.bool) =
  fun uu____7018  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____7023  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____7030  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____7035  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____7040  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____7045  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____7050  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____7055  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____7060  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____7065  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____7070  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____7075  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____7080  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____7087 = get_no_extract ()  in
    FStar_All.pipe_right uu____7087
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____7098  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____7103  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____7108  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____7113  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7120  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____7125  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____7130  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____7135  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____7140  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____7145  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____7150  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____7155  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____7160  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____7165  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7172  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____7177  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____7182  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____7187  ->
    let uu____7188 = get_smtencoding_nl_arith_repr ()  in
    uu____7188 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____7193  ->
    let uu____7194 = get_smtencoding_nl_arith_repr ()  in
    uu____7194 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____7199  ->
    let uu____7200 = get_smtencoding_nl_arith_repr ()  in
    uu____7200 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____7205  ->
    let uu____7206 = get_smtencoding_l_arith_repr ()  in
    uu____7206 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____7211  ->
    let uu____7212 = get_smtencoding_l_arith_repr ()  in
    uu____7212 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____7217  -> get_tactic_raw_binders () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____7222  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____7227  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____7232  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____7237  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____7242  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____7247  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____7252  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____7257  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____7262  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____7267  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____7272  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7279  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____7284  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____7297  ->
    let uu____7298 = get_using_facts_from ()  in
    match uu____7298 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7336  ->
    let uu____7337 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____7337
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7344  ->
    let uu____7345 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____7345 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7348 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7355  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____7360  ->
    let uu____7361 = get_smt ()  in
    match uu____7361 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7371  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____7376  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____7381  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7386  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____7391  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7396  ->
    (get_use_two_phase_tc ()) &&
      (let uu____7398 = lax ()  in Prims.op_Negation uu____7398)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7403  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7408  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7413  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7418  -> get_use_extracted_interfaces () 
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7425 = get_extract ()  in
    match uu____7425 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7436 =
            let uu____7449 = get_no_extract ()  in
            let uu____7452 = get_extract_namespace ()  in
            let uu____7455 = get_extract_module ()  in
            (uu____7449, uu____7452, uu____7455)  in
          match uu____7436 with
          | ([],[],[]) -> ()
          | uu____7470 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7518,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____7537 -> false  in
          let uu____7546 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____7580  ->
                    match uu____7580 with
                    | (path,uu____7588) -> matches_path m_components path))
             in
          match uu____7546 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____7599,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____7619 = get_extract_namespace ()  in
          match uu____7619 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____7635 = get_extract_module ()  in
          match uu____7635 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____7647 = no_extract m1  in Prims.op_Negation uu____7647) &&
          (let uu____7649 =
             let uu____7658 = get_extract_namespace ()  in
             let uu____7661 = get_extract_module ()  in
             (uu____7658, uu____7661)  in
           (match uu____7649 with
            | ([],[]) -> true
            | uu____7672 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  