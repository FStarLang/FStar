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
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : unit -> optionstate) =
  fun uu____483  ->
    let uu____484 =
      let uu____487 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____487  in
    FStar_List.hd uu____484
  
let (pop : unit -> unit) =
  fun uu____525  ->
    let uu____526 = FStar_ST.op_Bang fstar_options  in
    match uu____526 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____560::[] -> failwith "TOO MANY POPS!"
    | uu____567::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____608  ->
    let uu____609 =
      let uu____614 =
        let uu____617 =
          let uu____620 = FStar_ST.op_Bang fstar_options  in
          FStar_List.hd uu____620  in
        FStar_List.map FStar_Util.smap_copy uu____617  in
      let uu____654 = FStar_ST.op_Bang fstar_options  in uu____614 ::
        uu____654
       in
    FStar_ST.op_Colon_Equals fstar_options uu____609
  
let (internal_pop : unit -> Prims.bool) =
  fun uu____719  ->
    let curstack =
      let uu____723 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____723  in
    match curstack with
    | uu____757::[] -> false
    | uu____758::tl1 ->
        ((let uu____763 =
            let uu____768 =
              let uu____773 = FStar_ST.op_Bang fstar_options  in
              FStar_List.tl uu____773  in
            tl1 :: uu____768  in
          FStar_ST.op_Colon_Equals fstar_options uu____763);
         true)
  
let (internal_push : unit -> unit) =
  fun uu____840  ->
    let curstack =
      let uu____844 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____844  in
    let stack' =
      let uu____881 =
        let uu____882 = FStar_List.hd curstack  in
        FStar_Util.smap_copy uu____882  in
      uu____881 :: curstack  in
    let uu____885 =
      let uu____890 =
        let uu____895 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____895  in
      stack' :: uu____890  in
    FStar_ST.op_Colon_Equals fstar_options uu____885
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____963 = FStar_ST.op_Bang fstar_options  in
    match uu____963 with
    | [] -> failwith "set on empty option stack"
    | (uu____997::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
  
let (snapshot : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____1045  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____1069 = peek ()  in FStar_Util.smap_add uu____1069 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____1080  -> match uu____1080 with | (k,v1) -> set_option k v1 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____1109 =
      let uu____1112 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____1112
       in
    FStar_ST.op_Colon_Equals light_off_files uu____1109
  
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
  ("tactics_failhard", (Bool false));
  ("tactics_info", (Bool false));
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
  fun uu____1579  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1596  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1661 =
      let uu____1664 = peek ()  in FStar_Util.smap_try_find uu____1664 s  in
    match uu____1661 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1674 . Prims.string -> (option_val -> 'Auu____1674) -> 'Auu____1674
  = fun s  -> fun c  -> let uu____1690 = get_option s  in c uu____1690 
let (get_abort_on : unit -> Prims.int) =
  fun uu____1695  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1700  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1707  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1714  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1721  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1728  -> lookup_opt "cache_off" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1735  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1744  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1753  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1762  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____1769  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1776  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1783  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1788  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1793  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1800  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1807  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1812  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1821  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1834  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1843  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1850  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1855  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1860  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1867  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1874  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1879  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1886  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1893  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1898  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1903  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1908  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1915  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1922  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1927  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1932  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1937  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1942  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1947  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1952  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1957  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1964  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1971  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____1976  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1981  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1986  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1993  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____2000  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2007  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____2014  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____2019  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____2024  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____2029  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____2034  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____2039  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____2044  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____2049  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____2054  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2061  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____2068  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2075  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____2082  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____2087  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____2092  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____2097  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____2102  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____2107  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____2112  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____2117  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____2122  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____2127  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____2132  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____2137  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____2142  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____2147  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____2152  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____2157  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____2162  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2169  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____2176  ->
    let uu____2177 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____2177
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2186  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2199  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____2208  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____2217  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____2224  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____2229  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____2236  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____2243  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____2248  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____2253  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____2258  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____2263  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____2268  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____2273  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____2278  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____2283  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___82_2288  ->
    match uu___82_2288 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____2300 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____2306 = get_debug_level ()  in
    FStar_All.pipe_right uu____2306
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2439  ->
    let uu____2440 =
      let uu____2441 = FStar_ST.op_Bang _version  in
      let uu____2461 = FStar_ST.op_Bang _platform  in
      let uu____2481 = FStar_ST.op_Bang _compiler  in
      let uu____2501 = FStar_ST.op_Bang _date  in
      let uu____2521 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2441
        uu____2461 uu____2481 uu____2501 uu____2521
       in
    FStar_Util.print_string uu____2440
  
let display_usage_aux :
  'Auu____2547 'Auu____2548 .
    ('Auu____2547,Prims.string,'Auu____2548 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2596  ->
         match uu____2596 with
         | (uu____2607,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2619 =
                      let uu____2620 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2620  in
                    FStar_Util.print_string uu____2619
                  else
                    (let uu____2622 =
                       let uu____2623 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2623 doc  in
                     FStar_Util.print_string uu____2622)
              | FStar_Getopt.OneArg (uu____2624,argname) ->
                  if doc = ""
                  then
                    let uu____2632 =
                      let uu____2633 = FStar_Util.colorize_bold flag  in
                      let uu____2634 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2633 uu____2634
                       in
                    FStar_Util.print_string uu____2632
                  else
                    (let uu____2636 =
                       let uu____2637 = FStar_Util.colorize_bold flag  in
                       let uu____2638 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2637
                         uu____2638 doc
                        in
                     FStar_Util.print_string uu____2636))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2666 = o  in
    match uu____2666 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2702 =
                let uu____2703 = f ()  in set_option name uu____2703  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2718 = f x  in set_option name uu____2718
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2738 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2738  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2761 =
        let uu____2764 = lookup_opt name as_list'  in
        FStar_List.append uu____2764 [value]  in
      mk_list uu____2761
  
let accumulate_string :
  'Auu____2777 .
    Prims.string -> ('Auu____2777 -> Prims.string) -> 'Auu____2777 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2798 =
          let uu____2799 =
            let uu____2800 = post_processor value  in mk_string uu____2800
             in
          accumulated_option name uu____2799  in
        set_option name uu____2798
  
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
    match projectee with | Const _0 -> true | uu____2896 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2910 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2923 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2930 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2944 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2960 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2986 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____3025 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____3060 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____3074 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____3095 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____3133 -> true
    | uu____3134 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____3141 -> uu____3141
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___87_3159  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____3161 ->
                      let uu____3162 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____3162 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____3166 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____3166
                  | PathStr uu____3169 -> mk_path str_val
                  | SimpleStr uu____3170 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____3175 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____3190 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____3190
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
            let uu____3209 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____3209
  
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
    | PostProcessed (uu____3246,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____3256,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____3283 = desc_of_opt_type typ  in
      match uu____3283 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____3289  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____3306 =
      let uu____3307 = as_string s  in FStar_String.lowercase uu____3307  in
    mk_string uu____3306
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____3355  ->
    let uu____3367 =
      let uu____3379 =
        let uu____3391 =
          let uu____3403 =
            let uu____3413 =
              let uu____3414 = mk_bool true  in Const uu____3414  in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____3413,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
             in
          let uu____3416 =
            let uu____3428 =
              let uu____3440 =
                let uu____3450 =
                  let uu____3451 = mk_bool true  in Const uu____3451  in
                (FStar_Getopt.noshort, "cache_off", uu____3450,
                  "Do not read or write any .checked files")
                 in
              let uu____3453 =
                let uu____3465 =
                  let uu____3477 =
                    let uu____3489 =
                      let uu____3501 =
                        let uu____3513 =
                          let uu____3525 =
                            let uu____3537 =
                              let uu____3547 =
                                let uu____3548 = mk_bool true  in
                                Const uu____3548  in
                              (FStar_Getopt.noshort, "detail_errors",
                                uu____3547,
                                "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                               in
                            let uu____3550 =
                              let uu____3562 =
                                let uu____3572 =
                                  let uu____3573 = mk_bool true  in
                                  Const uu____3573  in
                                (FStar_Getopt.noshort, "detail_hint_replay",
                                  uu____3572,
                                  "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                 in
                              let uu____3575 =
                                let uu____3587 =
                                  let uu____3597 =
                                    let uu____3598 = mk_bool true  in
                                    Const uu____3598  in
                                  (FStar_Getopt.noshort, "doc", uu____3597,
                                    "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                   in
                                let uu____3600 =
                                  let uu____3612 =
                                    let uu____3624 =
                                      let uu____3634 =
                                        let uu____3635 = mk_bool true  in
                                        Const uu____3635  in
                                      (FStar_Getopt.noshort,
                                        "eager_inference", uu____3634,
                                        "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                       in
                                    let uu____3637 =
                                      let uu____3649 =
                                        let uu____3659 =
                                          let uu____3660 = mk_bool true  in
                                          Const uu____3660  in
                                        (FStar_Getopt.noshort,
                                          "eager_subtyping", uu____3659,
                                          "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                         in
                                      let uu____3662 =
                                        let uu____3674 =
                                          let uu____3686 =
                                            let uu____3698 =
                                              let uu____3710 =
                                                let uu____3720 =
                                                  let uu____3721 =
                                                    mk_bool true  in
                                                  Const uu____3721  in
                                                (FStar_Getopt.noshort,
                                                  "expose_interfaces",
                                                  uu____3720,
                                                  "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                 in
                                              let uu____3723 =
                                                let uu____3735 =
                                                  let uu____3745 =
                                                    let uu____3746 =
                                                      mk_bool true  in
                                                    Const uu____3746  in
                                                  (FStar_Getopt.noshort,
                                                    "hide_uvar_nums",
                                                    uu____3745,
                                                    "Don't print unification variable numbers")
                                                   in
                                                let uu____3748 =
                                                  let uu____3760 =
                                                    let uu____3772 =
                                                      let uu____3782 =
                                                        let uu____3783 =
                                                          mk_bool true  in
                                                        Const uu____3783  in
                                                      (FStar_Getopt.noshort,
                                                        "hint_info",
                                                        uu____3782,
                                                        "Print information regarding hints (deprecated; use --query_stats instead)")
                                                       in
                                                    let uu____3785 =
                                                      let uu____3797 =
                                                        let uu____3807 =
                                                          let uu____3808 =
                                                            mk_bool true  in
                                                          Const uu____3808
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "in", uu____3807,
                                                          "Legacy interactive mode; reads input from stdin")
                                                         in
                                                      let uu____3810 =
                                                        let uu____3822 =
                                                          let uu____3832 =
                                                            let uu____3833 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3833
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "ide",
                                                            uu____3832,
                                                            "JSON-based interactive mode for IDEs")
                                                           in
                                                        let uu____3835 =
                                                          let uu____3847 =
                                                            let uu____3859 =
                                                              let uu____3869
                                                                =
                                                                let uu____3870
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____3870
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "indent",
                                                                uu____3869,
                                                                "Parses and outputs the files on the command line")
                                                               in
                                                            let uu____3872 =
                                                              let uu____3884
                                                                =
                                                                let uu____3896
                                                                  =
                                                                  let uu____3908
                                                                    =
                                                                    let uu____3918
                                                                    =
                                                                    let uu____3919
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3919
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3918,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                  let uu____3921
                                                                    =
                                                                    let uu____3933
                                                                    =
                                                                    let uu____3945
                                                                    =
                                                                    let uu____3955
                                                                    =
                                                                    let uu____3956
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3956
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3955,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3958
                                                                    =
                                                                    let uu____3970
                                                                    =
                                                                    let uu____3980
                                                                    =
                                                                    let uu____3981
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3981
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3980,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3983
                                                                    =
                                                                    let uu____3995
                                                                    =
                                                                    let uu____4007
                                                                    =
                                                                    let uu____4019
                                                                    =
                                                                    let uu____4031
                                                                    =
                                                                    let uu____4041
                                                                    =
                                                                    let uu____4042
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4042
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____4041,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____4044
                                                                    =
                                                                    let uu____4056
                                                                    =
                                                                    let uu____4068
                                                                    =
                                                                    let uu____4078
                                                                    =
                                                                    let uu____4079
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4079
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____4078,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____4081
                                                                    =
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
                                                                    "no_location_info",
                                                                    uu____4115,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
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
                                                                    "no_smt",
                                                                    uu____4140,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
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
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____4165,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____4168
                                                                    =
                                                                    let uu____4180
                                                                    =
                                                                    let uu____4192
                                                                    =
                                                                    let uu____4204
                                                                    =
                                                                    let uu____4214
                                                                    =
                                                                    let uu____4215
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4215
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____4214,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____4217
                                                                    =
                                                                    let uu____4229
                                                                    =
                                                                    let uu____4239
                                                                    =
                                                                    let uu____4240
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4240
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____4239,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____4242
                                                                    =
                                                                    let uu____4254
                                                                    =
                                                                    let uu____4264
                                                                    =
                                                                    let uu____4265
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4265
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____4264,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____4267
                                                                    =
                                                                    let uu____4279
                                                                    =
                                                                    let uu____4289
                                                                    =
                                                                    let uu____4290
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4290
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____4289,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____4292
                                                                    =
                                                                    let uu____4304
                                                                    =
                                                                    let uu____4314
                                                                    =
                                                                    let uu____4315
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4315
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____4314,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____4317
                                                                    =
                                                                    let uu____4329
                                                                    =
                                                                    let uu____4339
                                                                    =
                                                                    let uu____4340
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4340
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____4339,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____4342
                                                                    =
                                                                    let uu____4354
                                                                    =
                                                                    let uu____4364
                                                                    =
                                                                    let uu____4365
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4365
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____4364,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____4367
                                                                    =
                                                                    let uu____4379
                                                                    =
                                                                    let uu____4389
                                                                    =
                                                                    let uu____4390
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4390
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____4389,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____4392
                                                                    =
                                                                    let uu____4404
                                                                    =
                                                                    let uu____4414
                                                                    =
                                                                    let uu____4415
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4415
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____4414,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____4417
                                                                    =
                                                                    let uu____4429
                                                                    =
                                                                    let uu____4441
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
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4451,
                                                                    " ")  in
                                                                    let uu____4454
                                                                    =
                                                                    let uu____4466
                                                                    =
                                                                    let uu____4478
                                                                    =
                                                                    let uu____4490
                                                                    =
                                                                    let uu____4502
                                                                    =
                                                                    let uu____4514
                                                                    =
                                                                    let uu____4524
                                                                    =
                                                                    let uu____4525
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4525
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4524,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4527
                                                                    =
                                                                    let uu____4539
                                                                    =
                                                                    let uu____4549
                                                                    =
                                                                    let uu____4550
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4550
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____4549,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____4552
                                                                    =
                                                                    let uu____4564
                                                                    =
                                                                    let uu____4574
                                                                    =
                                                                    let uu____4575
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4575
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____4574,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____4577
                                                                    =
                                                                    let uu____4589
                                                                    =
                                                                    let uu____4599
                                                                    =
                                                                    let uu____4600
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4600
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4599,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4602
                                                                    =
                                                                    let uu____4614
                                                                    =
                                                                    let uu____4626
                                                                    =
                                                                    let uu____4636
                                                                    =
                                                                    let uu____4637
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4637
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____4636,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____4639
                                                                    =
                                                                    let uu____4651
                                                                    =
                                                                    let uu____4663
                                                                    =
                                                                    let uu____4673
                                                                    =
                                                                    let uu____4674
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4674
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4673,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4676
                                                                    =
                                                                    let uu____4688
                                                                    =
                                                                    let uu____4698
                                                                    =
                                                                    let uu____4699
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4699
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4698,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4701
                                                                    =
                                                                    let uu____4713
                                                                    =
                                                                    let uu____4723
                                                                    =
                                                                    let uu____4724
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4724
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4723,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4726
                                                                    =
                                                                    let uu____4738
                                                                    =
                                                                    let uu____4748
                                                                    =
                                                                    let uu____4749
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4749
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4748,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4751
                                                                    =
                                                                    let uu____4763
                                                                    =
                                                                    let uu____4773
                                                                    =
                                                                    let uu____4774
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4774
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4773,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4776
                                                                    =
                                                                    let uu____4788
                                                                    =
                                                                    let uu____4798
                                                                    =
                                                                    let uu____4799
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4799
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4798,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4801
                                                                    =
                                                                    let uu____4813
                                                                    =
                                                                    let uu____4823
                                                                    =
                                                                    let uu____4824
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4824
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4823,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4826
                                                                    =
                                                                    let uu____4838
                                                                    =
                                                                    let uu____4848
                                                                    =
                                                                    let uu____4849
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4849
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4848,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4851
                                                                    =
                                                                    let uu____4863
                                                                    =
                                                                    let uu____4875
                                                                    =
                                                                    let uu____4885
                                                                    =
                                                                    let uu____4886
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4886
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____4885,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____4888
                                                                    =
                                                                    let uu____4900
                                                                    =
                                                                    let uu____4910
                                                                    =
                                                                    let uu____4911
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4911
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4910,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4913
                                                                    =
                                                                    let uu____4925
                                                                    =
                                                                    let uu____4937
                                                                    =
                                                                    let uu____4949
                                                                    =
                                                                    let uu____4961
                                                                    =
                                                                    let uu____4971
                                                                    =
                                                                    let uu____4972
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4972
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4971,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4974
                                                                    =
                                                                    let uu____4986
                                                                    =
                                                                    let uu____4996
                                                                    =
                                                                    let uu____4997
                                                                    =
                                                                    let uu____5005
                                                                    =
                                                                    let uu____5006
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5006
                                                                     in
                                                                    ((fun
                                                                    uu____5012
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____5005)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4997
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4996,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____5016
                                                                    =
                                                                    let uu____5028
                                                                    =
                                                                    let uu____5038
                                                                    =
                                                                    let uu____5039
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5039
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____5038,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____5041
                                                                    =
                                                                    let uu____5053
                                                                    =
                                                                    let uu____5065
                                                                    =
                                                                    let uu____5075
                                                                    =
                                                                    let uu____5076
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5076
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____5075,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____5078
                                                                    =
                                                                    let uu____5090
                                                                    =
                                                                    let uu____5102
                                                                    =
                                                                    let uu____5114
                                                                    =
                                                                    let uu____5126
                                                                    =
                                                                    let uu____5138
                                                                    =
                                                                    let uu____5148
                                                                    =
                                                                    let uu____5149
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5149
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____5148,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____5151
                                                                    =
                                                                    let uu____5163
                                                                    =
                                                                    let uu____5173
                                                                    =
                                                                    let uu____5174
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5174
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____5173,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____5176
                                                                    =
                                                                    let uu____5188
                                                                    =
                                                                    let uu____5200
                                                                    =
                                                                    let uu____5212
                                                                    =
                                                                    let uu____5222
                                                                    =
                                                                    let uu____5223
                                                                    =
                                                                    let uu____5231
                                                                    =
                                                                    let uu____5232
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5232
                                                                     in
                                                                    ((fun
                                                                    uu____5237
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____5231)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____5223
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____5222,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____5258
                                                                    =
                                                                    let uu____5270
                                                                    =
                                                                    let uu____5280
                                                                    =
                                                                    let uu____5281
                                                                    =
                                                                    let uu____5289
                                                                    =
                                                                    let uu____5290
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5290
                                                                     in
                                                                    ((fun
                                                                    uu____5295
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____5289)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____5281
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____5280,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____5316
                                                                    =
                                                                    let uu____5328
                                                                    =
                                                                    let uu____5338
                                                                    =
                                                                    let uu____5339
                                                                    =
                                                                    let uu____5347
                                                                    =
                                                                    let uu____5348
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5348
                                                                     in
                                                                    ((fun
                                                                    uu____5354
                                                                     ->
                                                                    (
                                                                    let uu____5356
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____5356);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____5347)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____5339
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____5338,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____5328]
                                                                     in
                                                                    uu____5270
                                                                    ::
                                                                    uu____5316
                                                                     in
                                                                    uu____5212
                                                                    ::
                                                                    uu____5258
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____5200
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____5188
                                                                     in
                                                                    uu____5163
                                                                    ::
                                                                    uu____5176
                                                                     in
                                                                    uu____5138
                                                                    ::
                                                                    uu____5151
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____5126
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____5114
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____5102
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____5090
                                                                     in
                                                                    uu____5065
                                                                    ::
                                                                    uu____5078
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____5053
                                                                     in
                                                                    uu____5028
                                                                    ::
                                                                    uu____5041
                                                                     in
                                                                    uu____4986
                                                                    ::
                                                                    uu____5016
                                                                     in
                                                                    uu____4961
                                                                    ::
                                                                    uu____4974
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4949
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4937
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4925
                                                                     in
                                                                    uu____4900
                                                                    ::
                                                                    uu____4913
                                                                     in
                                                                    uu____4875
                                                                    ::
                                                                    uu____4888
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4863
                                                                     in
                                                                    uu____4838
                                                                    ::
                                                                    uu____4851
                                                                     in
                                                                    uu____4813
                                                                    ::
                                                                    uu____4826
                                                                     in
                                                                    uu____4788
                                                                    ::
                                                                    uu____4801
                                                                     in
                                                                    uu____4763
                                                                    ::
                                                                    uu____4776
                                                                     in
                                                                    uu____4738
                                                                    ::
                                                                    uu____4751
                                                                     in
                                                                    uu____4713
                                                                    ::
                                                                    uu____4726
                                                                     in
                                                                    uu____4688
                                                                    ::
                                                                    uu____4701
                                                                     in
                                                                    uu____4663
                                                                    ::
                                                                    uu____4676
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____4651
                                                                     in
                                                                    uu____4626
                                                                    ::
                                                                    uu____4639
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4614
                                                                     in
                                                                    uu____4589
                                                                    ::
                                                                    uu____4602
                                                                     in
                                                                    uu____4564
                                                                    ::
                                                                    uu____4577
                                                                     in
                                                                    uu____4539
                                                                    ::
                                                                    uu____4552
                                                                     in
                                                                    uu____4514
                                                                    ::
                                                                    uu____4527
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4502
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4490
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4478
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4466
                                                                     in
                                                                    uu____4441
                                                                    ::
                                                                    uu____4454
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____4429
                                                                     in
                                                                    uu____4404
                                                                    ::
                                                                    uu____4417
                                                                     in
                                                                    uu____4379
                                                                    ::
                                                                    uu____4392
                                                                     in
                                                                    uu____4354
                                                                    ::
                                                                    uu____4367
                                                                     in
                                                                    uu____4329
                                                                    ::
                                                                    uu____4342
                                                                     in
                                                                    uu____4304
                                                                    ::
                                                                    uu____4317
                                                                     in
                                                                    uu____4279
                                                                    ::
                                                                    uu____4292
                                                                     in
                                                                    uu____4254
                                                                    ::
                                                                    uu____4267
                                                                     in
                                                                    uu____4229
                                                                    ::
                                                                    uu____4242
                                                                     in
                                                                    uu____4204
                                                                    ::
                                                                    uu____4217
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____4192
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____4180
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
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____4093
                                                                     in
                                                                    uu____4068
                                                                    ::
                                                                    uu____4081
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____4056
                                                                     in
                                                                    uu____4031
                                                                    ::
                                                                    uu____4044
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____4019
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____4007
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3995
                                                                     in
                                                                    uu____3970
                                                                    ::
                                                                    uu____3983
                                                                     in
                                                                    uu____3945
                                                                    ::
                                                                    uu____3958
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3933
                                                                     in
                                                                  uu____3908
                                                                    ::
                                                                    uu____3921
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_ifuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                  ::
                                                                  uu____3896
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_fuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of recursive functions to try initially (default 2)")
                                                                :: uu____3884
                                                               in
                                                            uu____3859 ::
                                                              uu____3872
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "include",
                                                            (ReverseAccumulated
                                                               (PathStr
                                                                  "path")),
                                                            "A directory in which to search for files included on the command line")
                                                            :: uu____3847
                                                           in
                                                        uu____3822 ::
                                                          uu____3835
                                                         in
                                                      uu____3797 ::
                                                        uu____3810
                                                       in
                                                    uu____3772 :: uu____3785
                                                     in
                                                  (FStar_Getopt.noshort,
                                                    "hint_file",
                                                    (PathStr "path"),
                                                    "Read/write hints to <path> (instead of module-specific hints files)")
                                                    :: uu____3760
                                                   in
                                                uu____3735 :: uu____3748  in
                                              uu____3710 :: uu____3723  in
                                            (FStar_Getopt.noshort,
                                              "extract_namespace",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "namespace name")))),
                                              "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                              :: uu____3698
                                             in
                                          (FStar_Getopt.noshort,
                                            "extract_module",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr "module_name")))),
                                            "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                            :: uu____3686
                                           in
                                        (FStar_Getopt.noshort, "extract",
                                          (Accumulated
                                             (SimpleStr
                                                "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                          "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                          :: uu____3674
                                         in
                                      uu____3649 :: uu____3662  in
                                    uu____3624 :: uu____3637  in
                                  (FStar_Getopt.noshort, "dump_module",
                                    (Accumulated (SimpleStr "module_name")),
                                    "") :: uu____3612
                                   in
                                uu____3587 :: uu____3600  in
                              uu____3562 :: uu____3575  in
                            uu____3537 :: uu____3550  in
                          (FStar_Getopt.noshort, "dep",
                            (EnumStr ["make"; "graph"; "full"]),
                            "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                            :: uu____3525
                           in
                        (FStar_Getopt.noshort, "defensive",
                          (EnumStr ["no"; "warn"; "fail"]),
                          "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                          :: uu____3513
                         in
                      (FStar_Getopt.noshort, "debug_level",
                        (Accumulated
                           (OpenEnumStr
                              (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                        "Control the verbosity of debugging info") ::
                        uu____3501
                       in
                    (FStar_Getopt.noshort, "debug",
                      (Accumulated (SimpleStr "module_name")),
                      "Print lots of debugging information while checking module")
                      :: uu____3489
                     in
                  (FStar_Getopt.noshort, "codegen-lib",
                    (Accumulated (SimpleStr "namespace")),
                    "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                    :: uu____3477
                   in
                (FStar_Getopt.noshort, "codegen",
                  (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                  "Generate code for further compilation to executable code, or build a compiler plugin")
                  :: uu____3465
                 in
              uu____3440 :: uu____3453  in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____3428
             in
          uu____3403 :: uu____3416  in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____3391
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____3379
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___83_6337  ->
             match uu___83_6337 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____3367

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____6360  ->
    let uu____6363 = specs_with_types ()  in
    FStar_List.map
      (fun uu____6390  ->
         match uu____6390 with
         | (short,long,typ,doc) ->
             let uu____6406 =
               let uu____6418 = arg_spec_of_opt_type long typ  in
               (short, long, uu____6418, doc)  in
             mk_spec uu____6406) uu____6363

let (settable : Prims.string -> Prims.bool) =
  fun uu___84_6428  ->
    match uu___84_6428 with
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
    | "tactics_failhard" -> true
    | "tactics_info" -> true
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
    | uu____6429 -> false
  
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
       (fun uu____6503  ->
          match uu____6503 with
          | (uu____6515,x,uu____6517,uu____6518) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____6580  ->
          match uu____6580 with
          | (uu____6592,x,uu____6594,uu____6595) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____6606  ->
    let uu____6607 = specs ()  in display_usage_aux uu____6607
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____6631 -> true
    | uu____6632 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____6639 -> uu____6639
  
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
        (fun uu___89_6656  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____6667 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____6667
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____6695  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____6700 =
             let uu____6703 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____6703 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____6700)
       in
    let uu____6752 =
      let uu____6755 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6755
       in
    (res, uu____6752)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6789  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6824 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6824 (fun x  -> ())  in
     (let uu____6830 =
        let uu____6835 =
          let uu____6836 = FStar_List.map mk_string old_verify_module  in
          List uu____6836  in
        ("verify_module", uu____6835)  in
      set_option' uu____6830);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6846 =
        let uu____6847 =
          let uu____6848 =
            let uu____6849 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6849  in
          (FStar_String.length f1) - uu____6848  in
        uu____6847 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6846  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6855 = get_lax ()  in
    if uu____6855
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6865 = module_name_of_file_name fn  in should_verify uu____6865
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6871 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6871
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6879 = should_verify m  in
    if uu____6879 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6887  ->
    let uu____6888 = get_no_default_includes ()  in
    if uu____6888
    then get_include ()
    else
      (let lib_paths =
         let uu____6895 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6895 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6904 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6904
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6918 =
         let uu____6921 = get_include ()  in
         FStar_List.append uu____6921 ["."]  in
       FStar_List.append lib_paths uu____6918)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____6934 = FStar_Util.smap_try_find file_map filename  in
    match uu____6934 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___91_6947  ->
               match () with
               | () ->
                   let uu____6950 = FStar_Util.is_path_absolute filename  in
                   if uu____6950
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____6957 =
                        let uu____6960 = include_path ()  in
                        FStar_List.rev uu____6960  in
                      FStar_Util.find_map uu____6957
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___90_6972 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____6983  ->
    let uu____6984 = get_prims ()  in
    match uu____6984 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6988 = find_file filename  in
        (match uu____6988 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6992 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6992)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6998  ->
    let uu____6999 = prims ()  in FStar_Util.basename uu____6999
  
let (pervasives : unit -> Prims.string) =
  fun uu____7004  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____7006 = find_file filename  in
    match uu____7006 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____7010 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____7010
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____7015  ->
    let uu____7016 = pervasives ()  in FStar_Util.basename uu____7016
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____7021  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____7023 = find_file filename  in
    match uu____7023 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____7027 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____7027
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____7033 = get_odir ()  in
    match uu____7033 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____7042 = get_cache_dir ()  in
    match uu____7042 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____7046 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____7046
  
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
             let uu____7112 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____7112  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____7120 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____7120 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____7190 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____7190 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____7199  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____7204  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7211  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____7216  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____7221  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____7227 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____7233 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____7239 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____7245 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____7252  ->
    let uu____7253 = get_codegen ()  in
    FStar_Util.map_opt uu____7253
      (fun uu___85_7257  ->
         match uu___85_7257 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____7258 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____7267  ->
    let uu____7268 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____7268
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____7285  -> let uu____7286 = get_debug ()  in uu____7286 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____7296 = get_debug ()  in
    FStar_All.pipe_right uu____7296 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____7313 = get_debug ()  in
       FStar_All.pipe_right uu____7313 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____7322  -> let uu____7323 = get_defensive ()  in uu____7323 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____7328  ->
    let uu____7329 = get_defensive ()  in uu____7329 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7336  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____7341  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____7346  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____7351  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____7357 = get_dump_module ()  in
    FStar_All.pipe_right uu____7357 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____7366  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____7371  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____7377 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____7377
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____7407  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____7412  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____7417  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7424  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____7429  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____7434  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____7439  ->
    let uu____7440 = get_initial_fuel ()  in
    let uu____7441 = get_max_fuel ()  in Prims.min uu____7440 uu____7441
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____7446  ->
    let uu____7447 = get_initial_ifuel ()  in
    let uu____7448 = get_max_ifuel ()  in Prims.min uu____7447 uu____7448
  
let (interactive : unit -> Prims.bool) =
  fun uu____7453  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____7458  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____7465  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____7470  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____7475  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____7480  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____7485  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____7490  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____7495  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____7500  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____7505  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____7510  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____7515  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____7522 = get_no_extract ()  in
    FStar_All.pipe_right uu____7522
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____7533  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____7538  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____7543  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____7548  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7555  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____7560  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____7565  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____7570  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____7575  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____7580  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____7585  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____7590  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____7595  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____7600  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7607  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____7612  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____7617  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____7622  ->
    let uu____7623 = get_smtencoding_nl_arith_repr ()  in
    uu____7623 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____7628  ->
    let uu____7629 = get_smtencoding_nl_arith_repr ()  in
    uu____7629 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____7634  ->
    let uu____7635 = get_smtencoding_nl_arith_repr ()  in
    uu____7635 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____7640  ->
    let uu____7641 = get_smtencoding_l_arith_repr ()  in
    uu____7641 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____7646  ->
    let uu____7647 = get_smtencoding_l_arith_repr ()  in
    uu____7647 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____7652  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____7657  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____7662  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____7667  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____7672  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____7677  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____7682  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____7687  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____7692  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____7697  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____7702  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____7707  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____7712  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____7717  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7724  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____7729  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____7742  ->
    let uu____7743 = get_using_facts_from ()  in
    match uu____7743 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7781  ->
    let uu____7782 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____7782
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7789  ->
    let uu____7790 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____7790 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7793 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7800  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____7805  ->
    let uu____7806 = get_smt ()  in
    match uu____7806 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7816  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____7821  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____7826  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7831  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____7836  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7841  ->
    (get_use_two_phase_tc ()) &&
      (let uu____7843 = lax ()  in Prims.op_Negation uu____7843)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7848  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7853  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7858  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7863  -> get_use_extracted_interfaces () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____7879 =
      let uu____7880 = trace_error ()  in Prims.op_Negation uu____7880  in
    if uu____7879
    then
      (push ();
       (try
          (fun uu___93_7885  ->
             match () with | () -> let retv = f ()  in (pop (); retv)) ()
        with | uu___92_7890 -> (pop (); FStar_Exn.raise uu___92_7890)))
    else (push (); (let retv = f ()  in pop (); retv))
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7902 = get_extract ()  in
    match uu____7902 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7913 =
            let uu____7926 = get_no_extract ()  in
            let uu____7929 = get_extract_namespace ()  in
            let uu____7932 = get_extract_module ()  in
            (uu____7926, uu____7929, uu____7932)  in
          match uu____7913 with
          | ([],[],[]) -> ()
          | uu____7947 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7995,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____8014 -> false  in
          let uu____8023 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____8057  ->
                    match uu____8057 with
                    | (path,uu____8065) -> matches_path m_components path))
             in
          match uu____8023 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____8076,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____8096 = get_extract_namespace ()  in
          match uu____8096 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____8112 = get_extract_module ()  in
          match uu____8112 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____8124 = no_extract m1  in Prims.op_Negation uu____8124) &&
          (let uu____8126 =
             let uu____8135 = get_extract_namespace ()  in
             let uu____8138 = get_extract_module ()  in
             (uu____8135, uu____8138)  in
           (match uu____8126 with
            | ([],[]) -> true
            | uu____8149 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  