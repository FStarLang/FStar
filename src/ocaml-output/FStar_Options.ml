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
  fun projectee  -> match projectee with | Low  -> true | uu____71 -> false 
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____82 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | High  -> true | uu____93 -> false 
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____104 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____117 -> false
  
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
    match projectee with | Bool _0 -> true | uu____172 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____196 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____220 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____244 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____269 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____294 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _0_1  -> Bool _0_1 
let (mk_string : Prims.string -> option_val) = fun _0_2  -> String _0_2 
let (mk_path : Prims.string -> option_val) = fun _0_3  -> Path _0_3 
let (mk_int : Prims.int -> option_val) = fun _0_4  -> Int _0_4 
let (mk_list : option_val Prims.list -> option_val) = fun _0_5  -> List _0_5 
type options =
  | Set 
  | Reset 
  | Restore 
let (uu___is_Set : options -> Prims.bool) =
  fun projectee  -> match projectee with | Set  -> true | uu____336 -> false 
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____347 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____358 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____383  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____410  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____438  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___80_467  ->
    match uu___80_467 with
    | Bool b -> b
    | uu____471 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___81_480  ->
    match uu___81_480 with
    | Int b -> b
    | uu____484 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___82_493  ->
    match uu___82_493 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____499 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___83_509  ->
    match uu___83_509 with
    | List ts -> ts
    | uu____515 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____526 .
    (option_val -> 'Auu____526) -> option_val -> 'Auu____526 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____544 = as_list' x  in
      FStar_All.pipe_right uu____544 (FStar_List.map as_t)
  
let as_option :
  'Auu____558 .
    (option_val -> 'Auu____558) ->
      option_val -> 'Auu____558 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___84_573  ->
      match uu___84_573 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____577 = as_t v1  in FStar_Pervasives_Native.Some uu____577
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___85_586  ->
    match uu___85_586 with
    | List ls ->
        let uu____593 =
          FStar_List.map
            (fun l  ->
               let uu____605 = as_string l  in FStar_Util.split uu____605 ",")
            ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____593
    | uu____617 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : unit -> optionstate) =
  fun uu____653  ->
    let uu____654 =
      let uu____657 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____657  in
    FStar_List.hd uu____654
  
let (pop : unit -> unit) =
  fun uu____696  ->
    let uu____697 = FStar_ST.op_Bang fstar_options  in
    match uu____697 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____732::[] -> failwith "TOO MANY POPS!"
    | uu____740::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____782  ->
    let uu____783 =
      let uu____788 =
        let uu____791 =
          let uu____794 = FStar_ST.op_Bang fstar_options  in
          FStar_List.hd uu____794  in
        FStar_List.map FStar_Util.smap_copy uu____791  in
      let uu____828 = FStar_ST.op_Bang fstar_options  in uu____788 ::
        uu____828
       in
    FStar_ST.op_Colon_Equals fstar_options uu____783
  
let (internal_pop : unit -> Prims.bool) =
  fun uu____895  ->
    let curstack =
      let uu____899 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____899  in
    match curstack with
    | [] -> failwith "impossible: empty current option stack"
    | uu____936::[] -> false
    | uu____938::tl1 ->
        ((let uu____943 =
            let uu____948 =
              let uu____953 = FStar_ST.op_Bang fstar_options  in
              FStar_List.tl uu____953  in
            tl1 :: uu____948  in
          FStar_ST.op_Colon_Equals fstar_options uu____943);
         true)
  
let (internal_push : unit -> unit) =
  fun uu____1022  ->
    let curstack =
      let uu____1026 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____1026  in
    let stack' =
      let uu____1063 =
        let uu____1064 = FStar_List.hd curstack  in
        FStar_Util.smap_copy uu____1064  in
      uu____1063 :: curstack  in
    let uu____1067 =
      let uu____1072 =
        let uu____1077 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____1077  in
      stack' :: uu____1072  in
    FStar_ST.op_Colon_Equals fstar_options uu____1067
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____1146 = FStar_ST.op_Bang fstar_options  in
    match uu____1146 with
    | [] -> failwith "set on empty option stack"
    | []::uu____1181 -> failwith "set on empty current option stack"
    | (uu____1189::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
  
let (snapshot : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____1239  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____1269 = peek ()  in FStar_Util.smap_add uu____1269 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____1282  -> match uu____1282 with | (k,v1) -> set_option k v1 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____1321 =
      let uu____1325 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____1325
       in
    FStar_ST.op_Colon_Equals light_off_files uu____1321
  
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
  ("cmi", (Bool false));
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
  ("print", (Bool false));
  ("print_in_place", (Bool false));
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
  ("use_extracted_interfaces", (Bool false));
  ("use_nbe", (Bool false))] 
let (init : unit -> unit) =
  fun uu____2204  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____2224  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____2297 =
      let uu____2300 = peek ()  in FStar_Util.smap_try_find uu____2300 s  in
    match uu____2297 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____2313 . Prims.string -> (option_val -> 'Auu____2313) -> 'Auu____2313
  = fun s  -> fun c  -> let uu____2331 = get_option s  in c uu____2331 
let (get_abort_on : unit -> Prims.int) =
  fun uu____2338  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____2347  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____2358  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____2370  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2381  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____2393  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____2402  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2413  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____2427  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____2441  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____2455  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____2466  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2477  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____2489  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____2498  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____2507  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____2518  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____2530  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____2539  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2552  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____2571  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____2585  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____2597  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____2606  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____2615  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2626  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____2638  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____2647  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____2658  -> lookup_opt "include" (as_list as_string) 
let (get_print : unit -> Prims.bool) =
  fun uu____2670  -> lookup_opt "print" as_bool 
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____2679  -> lookup_opt "print_in_place" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____2688  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____2697  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____2706  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____2717  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____2729  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____2738  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____2747  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____2756  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____2765  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____2774  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____2783  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____2792  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____2803  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____2815  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____2824  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____2833  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____2842  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2853  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____2865  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2876  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____2888  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____2897  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____2906  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____2915  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____2924  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____2933  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____2942  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____2951  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____2960  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2971  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____2983  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2994  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____3006  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____3015  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____3024  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____3033  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____3042  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____3051  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____3060  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____3069  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____3078  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____3087  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____3096  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____3105  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____3114  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____3123  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____3132  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____3141  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____3150  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3161  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____3173  ->
    let uu____3174 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____3174
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____3188  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3207  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____3221  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____3235  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____3247  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____3256  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____3267  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____3279  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____3288  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____3297  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____3306  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____3315  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____3324  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____3333  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____3342  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____3351  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____3360  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___86_3369  ->
    match uu___86_3369 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____3390 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____3399 = get_debug_level ()  in
    FStar_All.pipe_right uu____3399
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____3565  ->
    let uu____3566 =
      let uu____3568 = FStar_ST.op_Bang _version  in
      let uu____3591 = FStar_ST.op_Bang _platform  in
      let uu____3614 = FStar_ST.op_Bang _compiler  in
      let uu____3637 = FStar_ST.op_Bang _date  in
      let uu____3660 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____3568
        uu____3591 uu____3614 uu____3637 uu____3660
       in
    FStar_Util.print_string uu____3566
  
let display_usage_aux :
  'Auu____3691 'Auu____3692 .
    ('Auu____3691,Prims.string,'Auu____3692 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____3747  ->
         match uu____3747 with
         | (uu____3760,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____3779 =
                      let uu____3781 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____3781  in
                    FStar_Util.print_string uu____3779
                  else
                    (let uu____3786 =
                       let uu____3788 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____3788 doc  in
                     FStar_Util.print_string uu____3786)
              | FStar_Getopt.OneArg (uu____3791,argname) ->
                  if doc = ""
                  then
                    let uu____3806 =
                      let uu____3808 = FStar_Util.colorize_bold flag  in
                      let uu____3810 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____3808 uu____3810
                       in
                    FStar_Util.print_string uu____3806
                  else
                    (let uu____3815 =
                       let uu____3817 = FStar_Util.colorize_bold flag  in
                       let uu____3819 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____3817
                         uu____3819 doc
                        in
                     FStar_Util.print_string uu____3815))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____3854 = o  in
    match uu____3854 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____3896 =
                let uu____3897 = f ()  in set_option name uu____3897  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____3918 = f x  in set_option name uu____3918
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____3945 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____3945  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____3971 =
        let uu____3974 = lookup_opt name as_list'  in
        FStar_List.append uu____3974 [value]  in
      mk_list uu____3971
  
let accumulate_string :
  'Auu____3988 .
    Prims.string -> ('Auu____3988 -> Prims.string) -> 'Auu____3988 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____4013 =
          let uu____4014 =
            let uu____4015 = post_processor value  in mk_string uu____4015
             in
          accumulated_option name uu____4014  in
        set_option name uu____4013
  
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
    match projectee with | Const _0 -> true | uu____4137 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____4158 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____4180 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____4193 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____4217 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____4243 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____4280 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____4331 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____4372 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____4392 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____4419 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____4463 -> true
    | uu____4466 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____4477 -> uu____4477
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___91_4501  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____4503 ->
                      let uu____4505 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____4505 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____4513 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____4513
                  | PathStr uu____4530 -> mk_path str_val
                  | SimpleStr uu____4532 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____4542 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____4559 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____4559
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
            let uu____4579 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____4579
  
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
    | PostProcessed (uu____4649,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____4659,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____4690 = desc_of_opt_type typ  in
      match uu____4690 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____4698  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____4724 =
      let uu____4726 = as_string s  in FStar_String.lowercase uu____4726  in
    mk_string uu____4724
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____4783  ->
    let uu____4797 =
      let uu____4811 =
        let uu____4825 =
          let uu____4839 =
            let uu____4851 =
              let uu____4852 = mk_bool true  in Const uu____4852  in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____4851,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
             in
          let uu____4859 =
            let uu____4873 =
              let uu____4887 =
                let uu____4899 =
                  let uu____4900 = mk_bool true  in Const uu____4900  in
                (FStar_Getopt.noshort, "cache_off", uu____4899,
                  "Do not read or write any .checked files")
                 in
              let uu____4907 =
                let uu____4921 =
                  let uu____4933 =
                    let uu____4934 = mk_bool true  in Const uu____4934  in
                  (FStar_Getopt.noshort, "cmi", uu____4933,
                    "Inline across module interfaces during extraction (aka. cross-module inlining)")
                   in
                let uu____4941 =
                  let uu____4955 =
                    let uu____4969 =
                      let uu____4983 =
                        let uu____4997 =
                          let uu____5011 =
                            let uu____5025 =
                              let uu____5039 =
                                let uu____5051 =
                                  let uu____5052 = mk_bool true  in
                                  Const uu____5052  in
                                (FStar_Getopt.noshort, "detail_errors",
                                  uu____5051,
                                  "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                 in
                              let uu____5059 =
                                let uu____5073 =
                                  let uu____5085 =
                                    let uu____5086 = mk_bool true  in
                                    Const uu____5086  in
                                  (FStar_Getopt.noshort,
                                    "detail_hint_replay", uu____5085,
                                    "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                   in
                                let uu____5093 =
                                  let uu____5107 =
                                    let uu____5119 =
                                      let uu____5120 = mk_bool true  in
                                      Const uu____5120  in
                                    (FStar_Getopt.noshort, "doc", uu____5119,
                                      "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                     in
                                  let uu____5127 =
                                    let uu____5141 =
                                      let uu____5155 =
                                        let uu____5167 =
                                          let uu____5168 = mk_bool true  in
                                          Const uu____5168  in
                                        (FStar_Getopt.noshort,
                                          "eager_inference", uu____5167,
                                          "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                         in
                                      let uu____5175 =
                                        let uu____5189 =
                                          let uu____5201 =
                                            let uu____5202 = mk_bool true  in
                                            Const uu____5202  in
                                          (FStar_Getopt.noshort,
                                            "eager_subtyping", uu____5201,
                                            "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                           in
                                        let uu____5209 =
                                          let uu____5223 =
                                            let uu____5237 =
                                              let uu____5251 =
                                                let uu____5265 =
                                                  let uu____5277 =
                                                    let uu____5278 =
                                                      mk_bool true  in
                                                    Const uu____5278  in
                                                  (FStar_Getopt.noshort,
                                                    "expose_interfaces",
                                                    uu____5277,
                                                    "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                   in
                                                let uu____5285 =
                                                  let uu____5299 =
                                                    let uu____5311 =
                                                      let uu____5312 =
                                                        mk_bool true  in
                                                      Const uu____5312  in
                                                    (FStar_Getopt.noshort,
                                                      "hide_uvar_nums",
                                                      uu____5311,
                                                      "Don't print unification variable numbers")
                                                     in
                                                  let uu____5319 =
                                                    let uu____5333 =
                                                      let uu____5347 =
                                                        let uu____5359 =
                                                          let uu____5360 =
                                                            mk_bool true  in
                                                          Const uu____5360
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "hint_info",
                                                          uu____5359,
                                                          "Print information regarding hints (deprecated; use --query_stats instead)")
                                                         in
                                                      let uu____5367 =
                                                        let uu____5381 =
                                                          let uu____5393 =
                                                            let uu____5394 =
                                                              mk_bool true
                                                               in
                                                            Const uu____5394
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "in", uu____5393,
                                                            "Legacy interactive mode; reads input from stdin")
                                                           in
                                                        let uu____5401 =
                                                          let uu____5415 =
                                                            let uu____5427 =
                                                              let uu____5428
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____5428
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "ide",
                                                              uu____5427,
                                                              "JSON-based interactive mode for IDEs")
                                                             in
                                                          let uu____5435 =
                                                            let uu____5449 =
                                                              let uu____5463
                                                                =
                                                                let uu____5475
                                                                  =
                                                                  let uu____5476
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                  Const
                                                                    uu____5476
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "print",
                                                                  uu____5475,
                                                                  "Parses and prettyprints the files included on the command line")
                                                                 in
                                                              let uu____5483
                                                                =
                                                                let uu____5497
                                                                  =
                                                                  let uu____5509
                                                                    =
                                                                    let uu____5510
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5510
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "print_in_place",
                                                                    uu____5509,
                                                                    "Parses and prettyprints in place the files included on the command line")
                                                                   in
                                                                let uu____5517
                                                                  =
                                                                  let uu____5531
                                                                    =
                                                                    let uu____5545
                                                                    =
                                                                    let uu____5559
                                                                    =
                                                                    let uu____5571
                                                                    =
                                                                    let uu____5572
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5572
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____5571,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____5579
                                                                    =
                                                                    let uu____5593
                                                                    =
                                                                    let uu____5607
                                                                    =
                                                                    let uu____5619
                                                                    =
                                                                    let uu____5620
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5620
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____5619,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____5627
                                                                    =
                                                                    let uu____5641
                                                                    =
                                                                    let uu____5653
                                                                    =
                                                                    let uu____5654
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5654
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____5653,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____5661
                                                                    =
                                                                    let uu____5675
                                                                    =
                                                                    let uu____5689
                                                                    =
                                                                    let uu____5703
                                                                    =
                                                                    let uu____5717
                                                                    =
                                                                    let uu____5729
                                                                    =
                                                                    let uu____5730
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5730
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____5729,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____5737
                                                                    =
                                                                    let uu____5751
                                                                    =
                                                                    let uu____5765
                                                                    =
                                                                    let uu____5777
                                                                    =
                                                                    let uu____5778
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5778
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____5777,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____5785
                                                                    =
                                                                    let uu____5799
                                                                    =
                                                                    let uu____5813
                                                                    =
                                                                    let uu____5825
                                                                    =
                                                                    let uu____5826
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5826
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____5825,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____5833
                                                                    =
                                                                    let uu____5847
                                                                    =
                                                                    let uu____5859
                                                                    =
                                                                    let uu____5860
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5860
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____5859,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____5867
                                                                    =
                                                                    let uu____5881
                                                                    =
                                                                    let uu____5893
                                                                    =
                                                                    let uu____5894
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5894
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____5893,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____5901
                                                                    =
                                                                    let uu____5915
                                                                    =
                                                                    let uu____5929
                                                                    =
                                                                    let uu____5943
                                                                    =
                                                                    let uu____5955
                                                                    =
                                                                    let uu____5956
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5956
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____5955,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____5963
                                                                    =
                                                                    let uu____5977
                                                                    =
                                                                    let uu____5989
                                                                    =
                                                                    let uu____5990
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5990
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____5989,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____5997
                                                                    =
                                                                    let uu____6011
                                                                    =
                                                                    let uu____6023
                                                                    =
                                                                    let uu____6024
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6024
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____6023,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____6031
                                                                    =
                                                                    let uu____6045
                                                                    =
                                                                    let uu____6057
                                                                    =
                                                                    let uu____6058
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6058
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____6057,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____6065
                                                                    =
                                                                    let uu____6079
                                                                    =
                                                                    let uu____6091
                                                                    =
                                                                    let uu____6092
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6092
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____6091,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____6099
                                                                    =
                                                                    let uu____6113
                                                                    =
                                                                    let uu____6125
                                                                    =
                                                                    let uu____6126
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6126
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____6125,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____6133
                                                                    =
                                                                    let uu____6147
                                                                    =
                                                                    let uu____6159
                                                                    =
                                                                    let uu____6160
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6160
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____6159,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____6167
                                                                    =
                                                                    let uu____6181
                                                                    =
                                                                    let uu____6193
                                                                    =
                                                                    let uu____6194
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6194
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____6193,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____6201
                                                                    =
                                                                    let uu____6215
                                                                    =
                                                                    let uu____6227
                                                                    =
                                                                    let uu____6228
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6228
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____6227,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____6235
                                                                    =
                                                                    let uu____6249
                                                                    =
                                                                    let uu____6263
                                                                    =
                                                                    let uu____6275
                                                                    =
                                                                    let uu____6276
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6276
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____6275,
                                                                    " ")  in
                                                                    let uu____6283
                                                                    =
                                                                    let uu____6297
                                                                    =
                                                                    let uu____6311
                                                                    =
                                                                    let uu____6325
                                                                    =
                                                                    let uu____6339
                                                                    =
                                                                    let uu____6353
                                                                    =
                                                                    let uu____6365
                                                                    =
                                                                    let uu____6366
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6366
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____6365,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____6373
                                                                    =
                                                                    let uu____6387
                                                                    =
                                                                    let uu____6399
                                                                    =
                                                                    let uu____6400
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6400
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____6399,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____6407
                                                                    =
                                                                    let uu____6421
                                                                    =
                                                                    let uu____6433
                                                                    =
                                                                    let uu____6434
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6434
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____6433,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____6441
                                                                    =
                                                                    let uu____6455
                                                                    =
                                                                    let uu____6467
                                                                    =
                                                                    let uu____6468
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6468
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____6467,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____6475
                                                                    =
                                                                    let uu____6489
                                                                    =
                                                                    let uu____6503
                                                                    =
                                                                    let uu____6515
                                                                    =
                                                                    let uu____6516
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6516
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____6515,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____6523
                                                                    =
                                                                    let uu____6537
                                                                    =
                                                                    let uu____6551
                                                                    =
                                                                    let uu____6563
                                                                    =
                                                                    let uu____6564
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6564
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____6563,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____6571
                                                                    =
                                                                    let uu____6585
                                                                    =
                                                                    let uu____6597
                                                                    =
                                                                    let uu____6598
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6598
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____6597,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____6605
                                                                    =
                                                                    let uu____6619
                                                                    =
                                                                    let uu____6631
                                                                    =
                                                                    let uu____6632
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6632
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____6631,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____6639
                                                                    =
                                                                    let uu____6653
                                                                    =
                                                                    let uu____6665
                                                                    =
                                                                    let uu____6666
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6666
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____6665,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____6673
                                                                    =
                                                                    let uu____6687
                                                                    =
                                                                    let uu____6699
                                                                    =
                                                                    let uu____6700
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6700
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____6699,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____6707
                                                                    =
                                                                    let uu____6721
                                                                    =
                                                                    let uu____6733
                                                                    =
                                                                    let uu____6734
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6734
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____6733,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____6741
                                                                    =
                                                                    let uu____6755
                                                                    =
                                                                    let uu____6767
                                                                    =
                                                                    let uu____6768
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6768
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____6767,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____6775
                                                                    =
                                                                    let uu____6789
                                                                    =
                                                                    let uu____6801
                                                                    =
                                                                    let uu____6802
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6802
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____6801,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____6809
                                                                    =
                                                                    let uu____6823
                                                                    =
                                                                    let uu____6837
                                                                    =
                                                                    let uu____6849
                                                                    =
                                                                    let uu____6850
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6850
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____6849,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____6857
                                                                    =
                                                                    let uu____6871
                                                                    =
                                                                    let uu____6883
                                                                    =
                                                                    let uu____6884
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6884
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____6883,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____6891
                                                                    =
                                                                    let uu____6905
                                                                    =
                                                                    let uu____6919
                                                                    =
                                                                    let uu____6933
                                                                    =
                                                                    let uu____6947
                                                                    =
                                                                    let uu____6959
                                                                    =
                                                                    let uu____6960
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6960
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____6959,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____6967
                                                                    =
                                                                    let uu____6981
                                                                    =
                                                                    let uu____6993
                                                                    =
                                                                    let uu____6994
                                                                    =
                                                                    let uu____7002
                                                                    =
                                                                    let uu____7003
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7003
                                                                     in
                                                                    ((fun
                                                                    uu____7010
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____7002)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____6994
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____6993,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____7019
                                                                    =
                                                                    let uu____7033
                                                                    =
                                                                    let uu____7045
                                                                    =
                                                                    let uu____7046
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7046
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____7045,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____7053
                                                                    =
                                                                    let uu____7067
                                                                    =
                                                                    let uu____7081
                                                                    =
                                                                    let uu____7093
                                                                    =
                                                                    let uu____7094
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7094
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____7093,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____7101
                                                                    =
                                                                    let uu____7115
                                                                    =
                                                                    let uu____7129
                                                                    =
                                                                    let uu____7143
                                                                    =
                                                                    let uu____7157
                                                                    =
                                                                    let uu____7171
                                                                    =
                                                                    let uu____7183
                                                                    =
                                                                    let uu____7184
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7184
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____7183,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____7191
                                                                    =
                                                                    let uu____7205
                                                                    =
                                                                    let uu____7217
                                                                    =
                                                                    let uu____7218
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7218
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____7217,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____7225
                                                                    =
                                                                    let uu____7239
                                                                    =
                                                                    let uu____7253
                                                                    =
                                                                    let uu____7267
                                                                    =
                                                                    let uu____7281
                                                                    =
                                                                    let uu____7293
                                                                    =
                                                                    let uu____7294
                                                                    =
                                                                    let uu____7302
                                                                    =
                                                                    let uu____7303
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7303
                                                                     in
                                                                    ((fun
                                                                    uu____7309
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____7302)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7294
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____7293,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____7337
                                                                    =
                                                                    let uu____7351
                                                                    =
                                                                    let uu____7363
                                                                    =
                                                                    let uu____7364
                                                                    =
                                                                    let uu____7372
                                                                    =
                                                                    let uu____7373
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7373
                                                                     in
                                                                    ((fun
                                                                    uu____7379
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____7372)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7364
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____7363,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____7407
                                                                    =
                                                                    let uu____7421
                                                                    =
                                                                    let uu____7433
                                                                    =
                                                                    let uu____7434
                                                                    =
                                                                    let uu____7442
                                                                    =
                                                                    let uu____7443
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7443
                                                                     in
                                                                    ((fun
                                                                    uu____7450
                                                                     ->
                                                                    (
                                                                    let uu____7452
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____7452);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____7442)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7434
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____7433,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____7421]
                                                                     in
                                                                    uu____7351
                                                                    ::
                                                                    uu____7407
                                                                     in
                                                                    uu____7281
                                                                    ::
                                                                    uu____7337
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____7267
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____7253
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____7239
                                                                     in
                                                                    uu____7205
                                                                    ::
                                                                    uu____7225
                                                                     in
                                                                    uu____7171
                                                                    ::
                                                                    uu____7191
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____7157
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____7143
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____7129
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____7115
                                                                     in
                                                                    uu____7081
                                                                    ::
                                                                    uu____7101
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____7067
                                                                     in
                                                                    uu____7033
                                                                    ::
                                                                    uu____7053
                                                                     in
                                                                    uu____6981
                                                                    ::
                                                                    uu____7019
                                                                     in
                                                                    uu____6947
                                                                    ::
                                                                    uu____6967
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____6933
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____6919
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____6905
                                                                     in
                                                                    uu____6871
                                                                    ::
                                                                    uu____6891
                                                                     in
                                                                    uu____6837
                                                                    ::
                                                                    uu____6857
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____6823
                                                                     in
                                                                    uu____6789
                                                                    ::
                                                                    uu____6809
                                                                     in
                                                                    uu____6755
                                                                    ::
                                                                    uu____6775
                                                                     in
                                                                    uu____6721
                                                                    ::
                                                                    uu____6741
                                                                     in
                                                                    uu____6687
                                                                    ::
                                                                    uu____6707
                                                                     in
                                                                    uu____6653
                                                                    ::
                                                                    uu____6673
                                                                     in
                                                                    uu____6619
                                                                    ::
                                                                    uu____6639
                                                                     in
                                                                    uu____6585
                                                                    ::
                                                                    uu____6605
                                                                     in
                                                                    uu____6551
                                                                    ::
                                                                    uu____6571
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____6537
                                                                     in
                                                                    uu____6503
                                                                    ::
                                                                    uu____6523
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____6489
                                                                     in
                                                                    uu____6455
                                                                    ::
                                                                    uu____6475
                                                                     in
                                                                    uu____6421
                                                                    ::
                                                                    uu____6441
                                                                     in
                                                                    uu____6387
                                                                    ::
                                                                    uu____6407
                                                                     in
                                                                    uu____6353
                                                                    ::
                                                                    uu____6373
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6339
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6325
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____6311
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____6297
                                                                     in
                                                                    uu____6263
                                                                    ::
                                                                    uu____6283
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____6249
                                                                     in
                                                                    uu____6215
                                                                    ::
                                                                    uu____6235
                                                                     in
                                                                    uu____6181
                                                                    ::
                                                                    uu____6201
                                                                     in
                                                                    uu____6147
                                                                    ::
                                                                    uu____6167
                                                                     in
                                                                    uu____6113
                                                                    ::
                                                                    uu____6133
                                                                     in
                                                                    uu____6079
                                                                    ::
                                                                    uu____6099
                                                                     in
                                                                    uu____6045
                                                                    ::
                                                                    uu____6065
                                                                     in
                                                                    uu____6011
                                                                    ::
                                                                    uu____6031
                                                                     in
                                                                    uu____5977
                                                                    ::
                                                                    uu____5997
                                                                     in
                                                                    uu____5943
                                                                    ::
                                                                    uu____5963
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____5929
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____5915
                                                                     in
                                                                    uu____5881
                                                                    ::
                                                                    uu____5901
                                                                     in
                                                                    uu____5847
                                                                    ::
                                                                    uu____5867
                                                                     in
                                                                    uu____5813
                                                                    ::
                                                                    uu____5833
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____5799
                                                                     in
                                                                    uu____5765
                                                                    ::
                                                                    uu____5785
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____5751
                                                                     in
                                                                    uu____5717
                                                                    ::
                                                                    uu____5737
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____5703
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____5689
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____5675
                                                                     in
                                                                    uu____5641
                                                                    ::
                                                                    uu____5661
                                                                     in
                                                                    uu____5607
                                                                    ::
                                                                    uu____5627
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____5593
                                                                     in
                                                                    uu____5559
                                                                    ::
                                                                    uu____5579
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____5545
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (
                                                                    IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try initially (default 2)")
                                                                    ::
                                                                    uu____5531
                                                                   in
                                                                uu____5497 ::
                                                                  uu____5517
                                                                 in
                                                              uu____5463 ::
                                                                uu____5483
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "include",
                                                              (ReverseAccumulated
                                                                 (PathStr
                                                                    "path")),
                                                              "A directory in which to search for files included on the command line")
                                                              :: uu____5449
                                                             in
                                                          uu____5415 ::
                                                            uu____5435
                                                           in
                                                        uu____5381 ::
                                                          uu____5401
                                                         in
                                                      uu____5347 ::
                                                        uu____5367
                                                       in
                                                    (FStar_Getopt.noshort,
                                                      "hint_file",
                                                      (PathStr "path"),
                                                      "Read/write hints to <path> (instead of module-specific hints files)")
                                                      :: uu____5333
                                                     in
                                                  uu____5299 :: uu____5319
                                                   in
                                                uu____5265 :: uu____5285  in
                                              (FStar_Getopt.noshort,
                                                "extract_namespace",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "namespace name")))),
                                                "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                :: uu____5251
                                               in
                                            (FStar_Getopt.noshort,
                                              "extract_module",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "module_name")))),
                                              "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                              :: uu____5237
                                             in
                                          (FStar_Getopt.noshort, "extract",
                                            (Accumulated
                                               (SimpleStr
                                                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                            "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                            :: uu____5223
                                           in
                                        uu____5189 :: uu____5209  in
                                      uu____5155 :: uu____5175  in
                                    (FStar_Getopt.noshort, "dump_module",
                                      (Accumulated (SimpleStr "module_name")),
                                      "") :: uu____5141
                                     in
                                  uu____5107 :: uu____5127  in
                                uu____5073 :: uu____5093  in
                              uu____5039 :: uu____5059  in
                            (FStar_Getopt.noshort, "dep",
                              (EnumStr ["make"; "graph"; "full"; "raw"]),
                              "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                              :: uu____5025
                             in
                          (FStar_Getopt.noshort, "defensive",
                            (EnumStr ["no"; "warn"; "fail"]),
                            "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                            :: uu____5011
                           in
                        (FStar_Getopt.noshort, "debug_level",
                          (Accumulated
                             (OpenEnumStr
                                (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                          "Control the verbosity of debugging info") ::
                          uu____4997
                         in
                      (FStar_Getopt.noshort, "debug",
                        (Accumulated (SimpleStr "module_name")),
                        "Print lots of debugging information while checking module")
                        :: uu____4983
                       in
                    (FStar_Getopt.noshort, "codegen-lib",
                      (Accumulated (SimpleStr "namespace")),
                      "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                      :: uu____4969
                     in
                  (FStar_Getopt.noshort, "codegen",
                    (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                    "Generate code for further compilation to executable code, or build a compiler plugin")
                    :: uu____4955
                   in
                uu____4921 :: uu____4941  in
              uu____4887 :: uu____4907  in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____4873
             in
          uu____4839 :: uu____4859  in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____4825
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____4811
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___87_8940  ->
             match uu___87_8940 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____4797

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____8969  ->
    let uu____8972 = specs_with_types ()  in
    FStar_List.map
      (fun uu____9003  ->
         match uu____9003 with
         | (short,long,typ,doc) ->
             let uu____9025 =
               let uu____9039 = arg_spec_of_opt_type long typ  in
               (short, long, uu____9039, doc)  in
             mk_spec uu____9025) uu____8972

let (settable : Prims.string -> Prims.bool) =
  fun uu___88_9054  ->
    match uu___88_9054 with
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
    | uu____9177 -> false
  
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
       (fun uu____9276  ->
          match uu____9276 with
          | (uu____9291,x,uu____9293,uu____9294) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____9369  ->
          match uu____9369 with
          | (uu____9384,x,uu____9386,uu____9387) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____9403  ->
    let uu____9404 = specs ()  in display_usage_aux uu____9404
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____9436 -> true
    | uu____9439 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____9450 -> uu____9450
  
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
        (fun uu___93_9471  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____9488 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____9488
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____9524  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____9530 =
             let uu____9534 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____9534 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____9530)
       in
    let uu____9591 =
      let uu____9595 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____9595
       in
    (res, uu____9591)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____9637  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____9680 = specs ()  in
       FStar_Getopt.parse_cmdline uu____9680 (fun x  -> ())  in
     (let uu____9687 =
        let uu____9693 =
          let uu____9694 = FStar_List.map mk_string old_verify_module  in
          List uu____9694  in
        ("verify_module", uu____9693)  in
      set_option' uu____9687);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____9713 =
        let uu____9715 =
          let uu____9717 =
            let uu____9719 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____9719  in
          (FStar_String.length f1) - uu____9717  in
        uu____9715 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____9713  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____9732 = get_lax ()  in
    if uu____9732
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____9753 = module_name_of_file_name fn  in should_verify uu____9753
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____9764 = get___temp_no_proj ()  in
    FStar_List.contains m uu____9764
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____9778 = should_verify m  in
    if uu____9778 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____9795  ->
    let uu____9796 = get_no_default_includes ()  in
    if uu____9796
    then get_include ()
    else
      (let lib_paths =
         let uu____9808 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____9808 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____9824 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____9824
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____9851 =
         let uu____9855 = get_include ()  in
         FStar_List.append uu____9855 ["."]  in
       FStar_List.append lib_paths uu____9851)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____9881 = FStar_Util.smap_try_find file_map filename  in
    match uu____9881 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___95_9903  ->
               match () with
               | () ->
                   let uu____9907 = FStar_Util.is_path_absolute filename  in
                   if uu____9907
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____9923 =
                        let uu____9927 = include_path ()  in
                        FStar_List.rev uu____9927  in
                      FStar_Util.find_map uu____9923
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___94_9955 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____9975  ->
    let uu____9976 = get_prims ()  in
    match uu____9976 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____9985 = find_file filename  in
        (match uu____9985 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____9994 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____9994)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____10007  ->
    let uu____10008 = prims ()  in FStar_Util.basename uu____10008
  
let (pervasives : unit -> Prims.string) =
  fun uu____10016  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____10020 = find_file filename  in
    match uu____10020 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____10029 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____10029
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____10039  ->
    let uu____10040 = pervasives ()  in FStar_Util.basename uu____10040
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____10048  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____10052 = find_file filename  in
    match uu____10052 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____10061 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____10061
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____10074 = get_odir ()  in
    match uu____10074 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____10092 = get_cache_dir ()  in
    match uu____10092 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____10101 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____10101
  
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
             let uu____10198 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____10198  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____10221 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____10221 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____10317 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____10317 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____10332  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____10341  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10350  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____10357  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____10364  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____10371  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____10381 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____10392 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____10403 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____10414 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____10423  ->
    let uu____10424 = get_codegen ()  in
    FStar_Util.map_opt uu____10424
      (fun uu___89_10430  ->
         match uu___89_10430 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____10436 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____10449  ->
    let uu____10450 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____10450
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____10476  -> let uu____10477 = get_debug ()  in uu____10477 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____10494 = get_debug ()  in
    FStar_All.pipe_right uu____10494 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____10519 = get_debug ()  in
       FStar_All.pipe_right uu____10519 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____10534  ->
    let uu____10535 = get_defensive ()  in uu____10535 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____10545  ->
    let uu____10546 = get_defensive ()  in uu____10546 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10558  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____10565  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____10572  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____10579  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____10589 = get_dump_module ()  in
    FStar_All.pipe_right uu____10589 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____10604  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____10611  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____10621 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____10621
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____10657  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____10665  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____10672  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10681  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____10688  -> get_ide () 
let (print : unit -> Prims.bool) = fun uu____10695  -> get_print () 
let (print_in_place : unit -> Prims.bool) =
  fun uu____10702  -> get_print_in_place () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____10709  ->
    let uu____10710 = get_initial_fuel ()  in
    let uu____10712 = get_max_fuel ()  in Prims.min uu____10710 uu____10712
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____10720  ->
    let uu____10721 = get_initial_ifuel ()  in
    let uu____10723 = get_max_ifuel ()  in Prims.min uu____10721 uu____10723
  
let (interactive : unit -> Prims.bool) =
  fun uu____10731  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____10738  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____10747  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____10754  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____10761  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____10768  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____10775  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____10782  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____10789  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____10796  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____10802  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____10811  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____10818  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____10830 = get_no_extract ()  in
    FStar_All.pipe_right uu____10830
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____10849  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____10856  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____10863  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____10870  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10879  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____10886  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____10893  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____10900  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____10907  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____10914  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____10921  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____10928  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____10935  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____10942  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10951  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____10958  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____10965  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____10972  ->
    let uu____10973 = get_smtencoding_nl_arith_repr ()  in
    uu____10973 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____10983  ->
    let uu____10984 = get_smtencoding_nl_arith_repr ()  in
    uu____10984 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____10994  ->
    let uu____10995 = get_smtencoding_nl_arith_repr ()  in
    uu____10995 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____11005  ->
    let uu____11006 = get_smtencoding_l_arith_repr ()  in
    uu____11006 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____11016  ->
    let uu____11017 = get_smtencoding_l_arith_repr ()  in
    uu____11017 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____11027  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____11034  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____11041  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____11048  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____11055  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____11062  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____11069  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____11076  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____11083  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____11090  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____11097  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____11104  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____11111  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____11118  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11127  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____11134  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____11150  ->
    let uu____11151 = get_using_facts_from ()  in
    match uu____11151 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____11205  ->
    let uu____11206 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____11206
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____11217  ->
    let uu____11218 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____11218 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____11226 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____11237  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____11244  ->
    let uu____11245 = get_smt ()  in
    match uu____11245 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____11263  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____11270  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____11277  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____11284  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____11291  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____11298  ->
    (get_use_two_phase_tc ()) &&
      (let uu____11300 = lax ()  in Prims.op_Negation uu____11300)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____11308  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____11315  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____11322  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____11329  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____11336  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____11353 =
      let uu____11355 = trace_error ()  in Prims.op_Negation uu____11355  in
    if uu____11353
    then
      (push ();
       (let r =
          try
            (fun uu___97_11370  ->
               match () with
               | () -> let uu____11375 = f ()  in FStar_Util.Inr uu____11375)
              ()
          with | uu___96_11377 -> FStar_Util.Inl uu___96_11377  in
        pop ();
        (match r with
         | FStar_Util.Inr v1 -> v1
         | FStar_Util.Inl ex -> FStar_Exn.raise ex)))
    else (push (); (let retv = f ()  in pop (); retv))
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____11401 = get_extract ()  in
    match uu____11401 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____11416 =
            let uu____11432 = get_no_extract ()  in
            let uu____11436 = get_extract_namespace ()  in
            let uu____11440 = get_extract_module ()  in
            (uu____11432, uu____11436, uu____11440)  in
          match uu____11416 with
          | ([],[],[]) -> ()
          | uu____11465 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____11528,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____11561 -> false  in
          let uu____11573 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____11615  ->
                    match uu____11615 with
                    | (path,uu____11626) -> matches_path m_components path))
             in
          match uu____11573 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____11645,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____11675 = get_extract_namespace ()  in
          match uu____11675 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____11703 = get_extract_module ()  in
          match uu____11703 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____11725 = no_extract m1  in Prims.op_Negation uu____11725)
          &&
          (let uu____11728 =
             let uu____11739 = get_extract_namespace ()  in
             let uu____11743 = get_extract_module ()  in
             (uu____11739, uu____11743)  in
           (match uu____11728 with
            | ([],[]) -> true
            | uu____11763 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  