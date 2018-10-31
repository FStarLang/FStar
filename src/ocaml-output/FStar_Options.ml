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
  ("use_extracted_interfaces", (Bool false));
  ("use_nbe", (Bool false))] 
let (init : unit -> unit) =
  fun uu____2196  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____2216  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____2289 =
      let uu____2292 = peek ()  in FStar_Util.smap_try_find uu____2292 s  in
    match uu____2289 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____2305 . Prims.string -> (option_val -> 'Auu____2305) -> 'Auu____2305
  = fun s  -> fun c  -> let uu____2323 = get_option s  in c uu____2323 
let (get_abort_on : unit -> Prims.int) =
  fun uu____2330  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____2339  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____2350  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____2362  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2373  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____2385  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____2394  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2405  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____2419  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____2433  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____2447  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____2458  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2469  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____2481  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____2490  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____2499  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____2510  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____2522  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____2531  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2544  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____2563  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____2577  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____2589  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____2598  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____2607  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2618  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____2630  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____2639  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____2650  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____2662  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____2671  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____2680  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____2689  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____2700  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____2712  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____2721  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____2730  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____2739  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____2748  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____2757  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____2766  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____2775  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____2786  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____2798  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____2807  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____2816  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____2825  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2836  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____2848  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2859  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____2871  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____2880  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____2889  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____2898  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____2907  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____2916  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____2925  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____2934  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____2943  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2954  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____2966  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2977  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____2989  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____2998  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____3007  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____3016  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____3025  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____3034  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____3043  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____3052  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____3061  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____3070  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____3079  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____3088  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____3097  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____3106  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____3115  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____3124  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____3133  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3144  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____3156  ->
    let uu____3157 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____3157
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____3171  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3190  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____3204  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____3218  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____3230  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____3239  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____3250  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____3262  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____3271  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____3280  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____3289  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____3298  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____3307  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____3316  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____3325  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____3334  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____3343  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___86_3352  ->
    match uu___86_3352 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____3373 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____3382 = get_debug_level ()  in
    FStar_All.pipe_right uu____3382
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____3548  ->
    let uu____3549 =
      let uu____3551 = FStar_ST.op_Bang _version  in
      let uu____3574 = FStar_ST.op_Bang _platform  in
      let uu____3597 = FStar_ST.op_Bang _compiler  in
      let uu____3620 = FStar_ST.op_Bang _date  in
      let uu____3643 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____3551
        uu____3574 uu____3597 uu____3620 uu____3643
       in
    FStar_Util.print_string uu____3549
  
let display_usage_aux :
  'Auu____3674 'Auu____3675 .
    ('Auu____3674,Prims.string,'Auu____3675 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____3730  ->
         match uu____3730 with
         | (uu____3743,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____3762 =
                      let uu____3764 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____3764  in
                    FStar_Util.print_string uu____3762
                  else
                    (let uu____3769 =
                       let uu____3771 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____3771 doc  in
                     FStar_Util.print_string uu____3769)
              | FStar_Getopt.OneArg (uu____3774,argname) ->
                  if doc = ""
                  then
                    let uu____3789 =
                      let uu____3791 = FStar_Util.colorize_bold flag  in
                      let uu____3793 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____3791 uu____3793
                       in
                    FStar_Util.print_string uu____3789
                  else
                    (let uu____3798 =
                       let uu____3800 = FStar_Util.colorize_bold flag  in
                       let uu____3802 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____3800
                         uu____3802 doc
                        in
                     FStar_Util.print_string uu____3798))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____3837 = o  in
    match uu____3837 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____3879 =
                let uu____3880 = f ()  in set_option name uu____3880  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____3901 = f x  in set_option name uu____3901
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____3928 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____3928  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____3954 =
        let uu____3957 = lookup_opt name as_list'  in
        FStar_List.append uu____3957 [value]  in
      mk_list uu____3954
  
let accumulate_string :
  'Auu____3971 .
    Prims.string -> ('Auu____3971 -> Prims.string) -> 'Auu____3971 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____3996 =
          let uu____3997 =
            let uu____3998 = post_processor value  in mk_string uu____3998
             in
          accumulated_option name uu____3997  in
        set_option name uu____3996
  
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
    match projectee with | Const _0 -> true | uu____4120 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____4141 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____4163 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____4176 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____4200 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____4226 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____4263 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____4314 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____4355 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____4375 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____4402 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____4446 -> true
    | uu____4449 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____4460 -> uu____4460
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___91_4484  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____4486 ->
                      let uu____4488 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____4488 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____4496 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____4496
                  | PathStr uu____4513 -> mk_path str_val
                  | SimpleStr uu____4515 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____4525 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____4542 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____4542
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
            let uu____4562 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____4562
  
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
    | PostProcessed (uu____4632,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____4642,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____4673 = desc_of_opt_type typ  in
      match uu____4673 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____4681  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____4707 =
      let uu____4709 = as_string s  in FStar_String.lowercase uu____4709  in
    mk_string uu____4707
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____4766  ->
    let uu____4780 =
      let uu____4794 =
        let uu____4808 =
          let uu____4822 =
            let uu____4834 =
              let uu____4835 = mk_bool true  in Const uu____4835  in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____4834,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
             in
          let uu____4842 =
            let uu____4856 =
              let uu____4870 =
                let uu____4882 =
                  let uu____4883 = mk_bool true  in Const uu____4883  in
                (FStar_Getopt.noshort, "cache_off", uu____4882,
                  "Do not read or write any .checked files")
                 in
              let uu____4890 =
                let uu____4904 =
                  let uu____4916 =
                    let uu____4917 = mk_bool true  in Const uu____4917  in
                  (FStar_Getopt.noshort, "cmi", uu____4916,
                    "Inline across module interfaces during extraction (aka. cross-module inlining)")
                   in
                let uu____4924 =
                  let uu____4938 =
                    let uu____4952 =
                      let uu____4966 =
                        let uu____4980 =
                          let uu____4994 =
                            let uu____5008 =
                              let uu____5022 =
                                let uu____5034 =
                                  let uu____5035 = mk_bool true  in
                                  Const uu____5035  in
                                (FStar_Getopt.noshort, "detail_errors",
                                  uu____5034,
                                  "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                 in
                              let uu____5042 =
                                let uu____5056 =
                                  let uu____5068 =
                                    let uu____5069 = mk_bool true  in
                                    Const uu____5069  in
                                  (FStar_Getopt.noshort,
                                    "detail_hint_replay", uu____5068,
                                    "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                   in
                                let uu____5076 =
                                  let uu____5090 =
                                    let uu____5102 =
                                      let uu____5103 = mk_bool true  in
                                      Const uu____5103  in
                                    (FStar_Getopt.noshort, "doc", uu____5102,
                                      "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                     in
                                  let uu____5110 =
                                    let uu____5124 =
                                      let uu____5138 =
                                        let uu____5150 =
                                          let uu____5151 = mk_bool true  in
                                          Const uu____5151  in
                                        (FStar_Getopt.noshort,
                                          "eager_inference", uu____5150,
                                          "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                         in
                                      let uu____5158 =
                                        let uu____5172 =
                                          let uu____5184 =
                                            let uu____5185 = mk_bool true  in
                                            Const uu____5185  in
                                          (FStar_Getopt.noshort,
                                            "eager_subtyping", uu____5184,
                                            "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                           in
                                        let uu____5192 =
                                          let uu____5206 =
                                            let uu____5220 =
                                              let uu____5234 =
                                                let uu____5248 =
                                                  let uu____5260 =
                                                    let uu____5261 =
                                                      mk_bool true  in
                                                    Const uu____5261  in
                                                  (FStar_Getopt.noshort,
                                                    "expose_interfaces",
                                                    uu____5260,
                                                    "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                   in
                                                let uu____5268 =
                                                  let uu____5282 =
                                                    let uu____5294 =
                                                      let uu____5295 =
                                                        mk_bool true  in
                                                      Const uu____5295  in
                                                    (FStar_Getopt.noshort,
                                                      "hide_uvar_nums",
                                                      uu____5294,
                                                      "Don't print unification variable numbers")
                                                     in
                                                  let uu____5302 =
                                                    let uu____5316 =
                                                      let uu____5330 =
                                                        let uu____5342 =
                                                          let uu____5343 =
                                                            mk_bool true  in
                                                          Const uu____5343
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "hint_info",
                                                          uu____5342,
                                                          "Print information regarding hints (deprecated; use --query_stats instead)")
                                                         in
                                                      let uu____5350 =
                                                        let uu____5364 =
                                                          let uu____5376 =
                                                            let uu____5377 =
                                                              mk_bool true
                                                               in
                                                            Const uu____5377
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "in", uu____5376,
                                                            "Legacy interactive mode; reads input from stdin")
                                                           in
                                                        let uu____5384 =
                                                          let uu____5398 =
                                                            let uu____5410 =
                                                              let uu____5411
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____5411
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "ide",
                                                              uu____5410,
                                                              "JSON-based interactive mode for IDEs")
                                                             in
                                                          let uu____5418 =
                                                            let uu____5432 =
                                                              let uu____5446
                                                                =
                                                                let uu____5458
                                                                  =
                                                                  let uu____5459
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                  Const
                                                                    uu____5459
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "indent",
                                                                  uu____5458,
                                                                  "Parses and outputs the files on the command line")
                                                                 in
                                                              let uu____5466
                                                                =
                                                                let uu____5480
                                                                  =
                                                                  let uu____5494
                                                                    =
                                                                    let uu____5508
                                                                    =
                                                                    let uu____5520
                                                                    =
                                                                    let uu____5521
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5521
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____5520,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____5528
                                                                    =
                                                                    let uu____5542
                                                                    =
                                                                    let uu____5556
                                                                    =
                                                                    let uu____5568
                                                                    =
                                                                    let uu____5569
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5569
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____5568,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____5576
                                                                    =
                                                                    let uu____5590
                                                                    =
                                                                    let uu____5602
                                                                    =
                                                                    let uu____5603
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5603
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____5602,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____5610
                                                                    =
                                                                    let uu____5624
                                                                    =
                                                                    let uu____5638
                                                                    =
                                                                    let uu____5652
                                                                    =
                                                                    let uu____5666
                                                                    =
                                                                    let uu____5678
                                                                    =
                                                                    let uu____5679
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5679
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____5678,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____5686
                                                                    =
                                                                    let uu____5700
                                                                    =
                                                                    let uu____5714
                                                                    =
                                                                    let uu____5726
                                                                    =
                                                                    let uu____5727
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5727
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____5726,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____5734
                                                                    =
                                                                    let uu____5748
                                                                    =
                                                                    let uu____5762
                                                                    =
                                                                    let uu____5774
                                                                    =
                                                                    let uu____5775
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5775
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____5774,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____5782
                                                                    =
                                                                    let uu____5796
                                                                    =
                                                                    let uu____5808
                                                                    =
                                                                    let uu____5809
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5809
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____5808,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____5816
                                                                    =
                                                                    let uu____5830
                                                                    =
                                                                    let uu____5842
                                                                    =
                                                                    let uu____5843
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5843
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____5842,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____5850
                                                                    =
                                                                    let uu____5864
                                                                    =
                                                                    let uu____5878
                                                                    =
                                                                    let uu____5892
                                                                    =
                                                                    let uu____5904
                                                                    =
                                                                    let uu____5905
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5905
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____5904,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____5912
                                                                    =
                                                                    let uu____5926
                                                                    =
                                                                    let uu____5938
                                                                    =
                                                                    let uu____5939
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5939
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____5938,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____5946
                                                                    =
                                                                    let uu____5960
                                                                    =
                                                                    let uu____5972
                                                                    =
                                                                    let uu____5973
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5973
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____5972,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____5980
                                                                    =
                                                                    let uu____5994
                                                                    =
                                                                    let uu____6006
                                                                    =
                                                                    let uu____6007
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6007
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____6006,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____6014
                                                                    =
                                                                    let uu____6028
                                                                    =
                                                                    let uu____6040
                                                                    =
                                                                    let uu____6041
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6041
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____6040,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____6048
                                                                    =
                                                                    let uu____6062
                                                                    =
                                                                    let uu____6074
                                                                    =
                                                                    let uu____6075
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6075
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____6074,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____6082
                                                                    =
                                                                    let uu____6096
                                                                    =
                                                                    let uu____6108
                                                                    =
                                                                    let uu____6109
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6109
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____6108,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____6116
                                                                    =
                                                                    let uu____6130
                                                                    =
                                                                    let uu____6142
                                                                    =
                                                                    let uu____6143
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6143
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____6142,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____6150
                                                                    =
                                                                    let uu____6164
                                                                    =
                                                                    let uu____6176
                                                                    =
                                                                    let uu____6177
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6177
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____6176,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____6184
                                                                    =
                                                                    let uu____6198
                                                                    =
                                                                    let uu____6212
                                                                    =
                                                                    let uu____6224
                                                                    =
                                                                    let uu____6225
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6225
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____6224,
                                                                    " ")  in
                                                                    let uu____6232
                                                                    =
                                                                    let uu____6246
                                                                    =
                                                                    let uu____6260
                                                                    =
                                                                    let uu____6274
                                                                    =
                                                                    let uu____6288
                                                                    =
                                                                    let uu____6302
                                                                    =
                                                                    let uu____6314
                                                                    =
                                                                    let uu____6315
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6315
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____6314,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____6322
                                                                    =
                                                                    let uu____6336
                                                                    =
                                                                    let uu____6348
                                                                    =
                                                                    let uu____6349
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6349
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____6348,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____6356
                                                                    =
                                                                    let uu____6370
                                                                    =
                                                                    let uu____6382
                                                                    =
                                                                    let uu____6383
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6383
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____6382,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____6390
                                                                    =
                                                                    let uu____6404
                                                                    =
                                                                    let uu____6416
                                                                    =
                                                                    let uu____6417
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6417
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____6416,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____6424
                                                                    =
                                                                    let uu____6438
                                                                    =
                                                                    let uu____6452
                                                                    =
                                                                    let uu____6464
                                                                    =
                                                                    let uu____6465
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6465
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____6464,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____6472
                                                                    =
                                                                    let uu____6486
                                                                    =
                                                                    let uu____6500
                                                                    =
                                                                    let uu____6512
                                                                    =
                                                                    let uu____6513
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6513
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____6512,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____6520
                                                                    =
                                                                    let uu____6534
                                                                    =
                                                                    let uu____6546
                                                                    =
                                                                    let uu____6547
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6547
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____6546,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____6554
                                                                    =
                                                                    let uu____6568
                                                                    =
                                                                    let uu____6580
                                                                    =
                                                                    let uu____6581
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6581
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____6580,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____6588
                                                                    =
                                                                    let uu____6602
                                                                    =
                                                                    let uu____6614
                                                                    =
                                                                    let uu____6615
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6615
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____6614,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____6622
                                                                    =
                                                                    let uu____6636
                                                                    =
                                                                    let uu____6648
                                                                    =
                                                                    let uu____6649
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6649
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____6648,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____6656
                                                                    =
                                                                    let uu____6670
                                                                    =
                                                                    let uu____6682
                                                                    =
                                                                    let uu____6683
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6683
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____6682,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____6690
                                                                    =
                                                                    let uu____6704
                                                                    =
                                                                    let uu____6716
                                                                    =
                                                                    let uu____6717
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6717
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____6716,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____6724
                                                                    =
                                                                    let uu____6738
                                                                    =
                                                                    let uu____6750
                                                                    =
                                                                    let uu____6751
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6751
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____6750,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____6758
                                                                    =
                                                                    let uu____6772
                                                                    =
                                                                    let uu____6786
                                                                    =
                                                                    let uu____6798
                                                                    =
                                                                    let uu____6799
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6799
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____6798,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____6806
                                                                    =
                                                                    let uu____6820
                                                                    =
                                                                    let uu____6832
                                                                    =
                                                                    let uu____6833
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6833
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____6832,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____6840
                                                                    =
                                                                    let uu____6854
                                                                    =
                                                                    let uu____6868
                                                                    =
                                                                    let uu____6882
                                                                    =
                                                                    let uu____6896
                                                                    =
                                                                    let uu____6908
                                                                    =
                                                                    let uu____6909
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6909
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____6908,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____6916
                                                                    =
                                                                    let uu____6930
                                                                    =
                                                                    let uu____6942
                                                                    =
                                                                    let uu____6943
                                                                    =
                                                                    let uu____6951
                                                                    =
                                                                    let uu____6952
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6952
                                                                     in
                                                                    ((fun
                                                                    uu____6959
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____6951)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____6943
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____6942,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____6968
                                                                    =
                                                                    let uu____6982
                                                                    =
                                                                    let uu____6994
                                                                    =
                                                                    let uu____6995
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6995
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____6994,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____7002
                                                                    =
                                                                    let uu____7016
                                                                    =
                                                                    let uu____7030
                                                                    =
                                                                    let uu____7042
                                                                    =
                                                                    let uu____7043
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7043
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____7042,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____7050
                                                                    =
                                                                    let uu____7064
                                                                    =
                                                                    let uu____7078
                                                                    =
                                                                    let uu____7092
                                                                    =
                                                                    let uu____7106
                                                                    =
                                                                    let uu____7120
                                                                    =
                                                                    let uu____7132
                                                                    =
                                                                    let uu____7133
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7133
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____7132,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____7140
                                                                    =
                                                                    let uu____7154
                                                                    =
                                                                    let uu____7166
                                                                    =
                                                                    let uu____7167
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7167
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____7166,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____7174
                                                                    =
                                                                    let uu____7188
                                                                    =
                                                                    let uu____7202
                                                                    =
                                                                    let uu____7216
                                                                    =
                                                                    let uu____7230
                                                                    =
                                                                    let uu____7242
                                                                    =
                                                                    let uu____7243
                                                                    =
                                                                    let uu____7251
                                                                    =
                                                                    let uu____7252
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7252
                                                                     in
                                                                    ((fun
                                                                    uu____7258
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____7251)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7243
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____7242,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____7286
                                                                    =
                                                                    let uu____7300
                                                                    =
                                                                    let uu____7312
                                                                    =
                                                                    let uu____7313
                                                                    =
                                                                    let uu____7321
                                                                    =
                                                                    let uu____7322
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7322
                                                                     in
                                                                    ((fun
                                                                    uu____7328
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____7321)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7313
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____7312,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____7356
                                                                    =
                                                                    let uu____7370
                                                                    =
                                                                    let uu____7382
                                                                    =
                                                                    let uu____7383
                                                                    =
                                                                    let uu____7391
                                                                    =
                                                                    let uu____7392
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7392
                                                                     in
                                                                    ((fun
                                                                    uu____7399
                                                                     ->
                                                                    (
                                                                    let uu____7401
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____7401);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____7391)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7383
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____7382,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____7370]
                                                                     in
                                                                    uu____7300
                                                                    ::
                                                                    uu____7356
                                                                     in
                                                                    uu____7230
                                                                    ::
                                                                    uu____7286
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____7216
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____7202
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____7188
                                                                     in
                                                                    uu____7154
                                                                    ::
                                                                    uu____7174
                                                                     in
                                                                    uu____7120
                                                                    ::
                                                                    uu____7140
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____7106
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____7092
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____7078
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____7064
                                                                     in
                                                                    uu____7030
                                                                    ::
                                                                    uu____7050
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____7016
                                                                     in
                                                                    uu____6982
                                                                    ::
                                                                    uu____7002
                                                                     in
                                                                    uu____6930
                                                                    ::
                                                                    uu____6968
                                                                     in
                                                                    uu____6896
                                                                    ::
                                                                    uu____6916
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____6882
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____6868
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____6854
                                                                     in
                                                                    uu____6820
                                                                    ::
                                                                    uu____6840
                                                                     in
                                                                    uu____6786
                                                                    ::
                                                                    uu____6806
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____6772
                                                                     in
                                                                    uu____6738
                                                                    ::
                                                                    uu____6758
                                                                     in
                                                                    uu____6704
                                                                    ::
                                                                    uu____6724
                                                                     in
                                                                    uu____6670
                                                                    ::
                                                                    uu____6690
                                                                     in
                                                                    uu____6636
                                                                    ::
                                                                    uu____6656
                                                                     in
                                                                    uu____6602
                                                                    ::
                                                                    uu____6622
                                                                     in
                                                                    uu____6568
                                                                    ::
                                                                    uu____6588
                                                                     in
                                                                    uu____6534
                                                                    ::
                                                                    uu____6554
                                                                     in
                                                                    uu____6500
                                                                    ::
                                                                    uu____6520
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____6486
                                                                     in
                                                                    uu____6452
                                                                    ::
                                                                    uu____6472
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____6438
                                                                     in
                                                                    uu____6404
                                                                    ::
                                                                    uu____6424
                                                                     in
                                                                    uu____6370
                                                                    ::
                                                                    uu____6390
                                                                     in
                                                                    uu____6336
                                                                    ::
                                                                    uu____6356
                                                                     in
                                                                    uu____6302
                                                                    ::
                                                                    uu____6322
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6288
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6274
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____6260
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____6246
                                                                     in
                                                                    uu____6212
                                                                    ::
                                                                    uu____6232
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____6198
                                                                     in
                                                                    uu____6164
                                                                    ::
                                                                    uu____6184
                                                                     in
                                                                    uu____6130
                                                                    ::
                                                                    uu____6150
                                                                     in
                                                                    uu____6096
                                                                    ::
                                                                    uu____6116
                                                                     in
                                                                    uu____6062
                                                                    ::
                                                                    uu____6082
                                                                     in
                                                                    uu____6028
                                                                    ::
                                                                    uu____6048
                                                                     in
                                                                    uu____5994
                                                                    ::
                                                                    uu____6014
                                                                     in
                                                                    uu____5960
                                                                    ::
                                                                    uu____5980
                                                                     in
                                                                    uu____5926
                                                                    ::
                                                                    uu____5946
                                                                     in
                                                                    uu____5892
                                                                    ::
                                                                    uu____5912
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____5878
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____5864
                                                                     in
                                                                    uu____5830
                                                                    ::
                                                                    uu____5850
                                                                     in
                                                                    uu____5796
                                                                    ::
                                                                    uu____5816
                                                                     in
                                                                    uu____5762
                                                                    ::
                                                                    uu____5782
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____5748
                                                                     in
                                                                    uu____5714
                                                                    ::
                                                                    uu____5734
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____5700
                                                                     in
                                                                    uu____5666
                                                                    ::
                                                                    uu____5686
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____5652
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____5638
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____5624
                                                                     in
                                                                    uu____5590
                                                                    ::
                                                                    uu____5610
                                                                     in
                                                                    uu____5556
                                                                    ::
                                                                    uu____5576
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____5542
                                                                     in
                                                                    uu____5508
                                                                    ::
                                                                    uu____5528
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (
                                                                    IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____5494
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_fuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of recursive functions to try initially (default 2)")
                                                                  ::
                                                                  uu____5480
                                                                 in
                                                              uu____5446 ::
                                                                uu____5466
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "include",
                                                              (ReverseAccumulated
                                                                 (PathStr
                                                                    "path")),
                                                              "A directory in which to search for files included on the command line")
                                                              :: uu____5432
                                                             in
                                                          uu____5398 ::
                                                            uu____5418
                                                           in
                                                        uu____5364 ::
                                                          uu____5384
                                                         in
                                                      uu____5330 ::
                                                        uu____5350
                                                       in
                                                    (FStar_Getopt.noshort,
                                                      "hint_file",
                                                      (PathStr "path"),
                                                      "Read/write hints to <path> (instead of module-specific hints files)")
                                                      :: uu____5316
                                                     in
                                                  uu____5282 :: uu____5302
                                                   in
                                                uu____5248 :: uu____5268  in
                                              (FStar_Getopt.noshort,
                                                "extract_namespace",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "namespace name")))),
                                                "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                :: uu____5234
                                               in
                                            (FStar_Getopt.noshort,
                                              "extract_module",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "module_name")))),
                                              "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                              :: uu____5220
                                             in
                                          (FStar_Getopt.noshort, "extract",
                                            (Accumulated
                                               (SimpleStr
                                                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                            "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                            :: uu____5206
                                           in
                                        uu____5172 :: uu____5192  in
                                      uu____5138 :: uu____5158  in
                                    (FStar_Getopt.noshort, "dump_module",
                                      (Accumulated (SimpleStr "module_name")),
                                      "") :: uu____5124
                                     in
                                  uu____5090 :: uu____5110  in
                                uu____5056 :: uu____5076  in
                              uu____5022 :: uu____5042  in
                            (FStar_Getopt.noshort, "dep",
                              (EnumStr ["make"; "graph"; "full"; "raw"]),
                              "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                              :: uu____5008
                             in
                          (FStar_Getopt.noshort, "defensive",
                            (EnumStr ["no"; "warn"; "fail"]),
                            "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                            :: uu____4994
                           in
                        (FStar_Getopt.noshort, "debug_level",
                          (Accumulated
                             (OpenEnumStr
                                (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                          "Control the verbosity of debugging info") ::
                          uu____4980
                         in
                      (FStar_Getopt.noshort, "debug",
                        (Accumulated (SimpleStr "module_name")),
                        "Print lots of debugging information while checking module")
                        :: uu____4966
                       in
                    (FStar_Getopt.noshort, "codegen-lib",
                      (Accumulated (SimpleStr "namespace")),
                      "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                      :: uu____4952
                     in
                  (FStar_Getopt.noshort, "codegen",
                    (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                    "Generate code for further compilation to executable code, or build a compiler plugin")
                    :: uu____4938
                   in
                uu____4904 :: uu____4924  in
              uu____4870 :: uu____4890  in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____4856
             in
          uu____4822 :: uu____4842  in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____4808
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____4794
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___87_8878  ->
             match uu___87_8878 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____4780

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____8907  ->
    let uu____8910 = specs_with_types ()  in
    FStar_List.map
      (fun uu____8941  ->
         match uu____8941 with
         | (short,long,typ,doc) ->
             let uu____8963 =
               let uu____8977 = arg_spec_of_opt_type long typ  in
               (short, long, uu____8977, doc)  in
             mk_spec uu____8963) uu____8910

let (settable : Prims.string -> Prims.bool) =
  fun uu___88_8992  ->
    match uu___88_8992 with
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
    | uu____9115 -> false
  
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
       (fun uu____9214  ->
          match uu____9214 with
          | (uu____9229,x,uu____9231,uu____9232) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____9307  ->
          match uu____9307 with
          | (uu____9322,x,uu____9324,uu____9325) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____9341  ->
    let uu____9342 = specs ()  in display_usage_aux uu____9342
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____9374 -> true
    | uu____9377 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____9388 -> uu____9388
  
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
        (fun uu___93_9409  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____9426 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____9426
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____9462  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____9468 =
             let uu____9472 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____9472 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____9468)
       in
    let uu____9529 =
      let uu____9533 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____9533
       in
    (res, uu____9529)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____9575  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____9618 = specs ()  in
       FStar_Getopt.parse_cmdline uu____9618 (fun x  -> ())  in
     (let uu____9625 =
        let uu____9631 =
          let uu____9632 = FStar_List.map mk_string old_verify_module  in
          List uu____9632  in
        ("verify_module", uu____9631)  in
      set_option' uu____9625);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____9651 =
        let uu____9653 =
          let uu____9655 =
            let uu____9657 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____9657  in
          (FStar_String.length f1) - uu____9655  in
        uu____9653 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____9651  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____9670 = get_lax ()  in
    if uu____9670
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____9691 = module_name_of_file_name fn  in should_verify uu____9691
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____9702 = get___temp_no_proj ()  in
    FStar_List.contains m uu____9702
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____9716 = should_verify m  in
    if uu____9716 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____9733  ->
    let uu____9734 = get_no_default_includes ()  in
    if uu____9734
    then get_include ()
    else
      (let lib_paths =
         let uu____9746 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____9746 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____9762 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____9762
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____9789 =
         let uu____9793 = get_include ()  in
         FStar_List.append uu____9793 ["."]  in
       FStar_List.append lib_paths uu____9789)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____9819 = FStar_Util.smap_try_find file_map filename  in
    match uu____9819 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___95_9841  ->
               match () with
               | () ->
                   let uu____9845 = FStar_Util.is_path_absolute filename  in
                   if uu____9845
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____9861 =
                        let uu____9865 = include_path ()  in
                        FStar_List.rev uu____9865  in
                      FStar_Util.find_map uu____9861
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___94_9893 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____9913  ->
    let uu____9914 = get_prims ()  in
    match uu____9914 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____9923 = find_file filename  in
        (match uu____9923 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____9932 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____9932)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____9945  ->
    let uu____9946 = prims ()  in FStar_Util.basename uu____9946
  
let (pervasives : unit -> Prims.string) =
  fun uu____9954  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____9958 = find_file filename  in
    match uu____9958 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____9967 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____9967
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____9977  ->
    let uu____9978 = pervasives ()  in FStar_Util.basename uu____9978
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____9986  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____9990 = find_file filename  in
    match uu____9990 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____9999 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____9999
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____10012 = get_odir ()  in
    match uu____10012 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____10030 = get_cache_dir ()  in
    match uu____10030 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____10039 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____10039
  
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
             let uu____10136 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____10136  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____10159 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____10159 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____10255 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____10255 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____10270  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____10279  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10288  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____10295  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____10302  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____10309  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____10319 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____10330 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____10341 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____10352 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____10361  ->
    let uu____10362 = get_codegen ()  in
    FStar_Util.map_opt uu____10362
      (fun uu___89_10368  ->
         match uu___89_10368 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____10374 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____10387  ->
    let uu____10388 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____10388
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____10414  -> let uu____10415 = get_debug ()  in uu____10415 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____10432 = get_debug ()  in
    FStar_All.pipe_right uu____10432 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____10457 = get_debug ()  in
       FStar_All.pipe_right uu____10457 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____10472  ->
    let uu____10473 = get_defensive ()  in uu____10473 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____10483  ->
    let uu____10484 = get_defensive ()  in uu____10484 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10496  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____10503  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____10510  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____10517  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____10527 = get_dump_module ()  in
    FStar_All.pipe_right uu____10527 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____10542  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____10549  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____10559 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____10559
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____10595  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____10603  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____10610  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10619  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____10626  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____10633  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____10640  ->
    let uu____10641 = get_initial_fuel ()  in
    let uu____10643 = get_max_fuel ()  in Prims.min uu____10641 uu____10643
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____10651  ->
    let uu____10652 = get_initial_ifuel ()  in
    let uu____10654 = get_max_ifuel ()  in Prims.min uu____10652 uu____10654
  
let (interactive : unit -> Prims.bool) =
  fun uu____10662  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____10669  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____10678  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____10685  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____10692  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____10699  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____10706  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____10713  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____10720  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____10727  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____10733  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____10742  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____10749  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____10761 = get_no_extract ()  in
    FStar_All.pipe_right uu____10761
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____10780  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____10787  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____10794  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____10801  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10810  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____10817  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____10824  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____10831  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____10838  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____10845  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____10852  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____10859  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____10866  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____10873  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10882  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____10889  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____10896  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____10903  ->
    let uu____10904 = get_smtencoding_nl_arith_repr ()  in
    uu____10904 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____10914  ->
    let uu____10915 = get_smtencoding_nl_arith_repr ()  in
    uu____10915 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____10925  ->
    let uu____10926 = get_smtencoding_nl_arith_repr ()  in
    uu____10926 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____10936  ->
    let uu____10937 = get_smtencoding_l_arith_repr ()  in
    uu____10937 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____10947  ->
    let uu____10948 = get_smtencoding_l_arith_repr ()  in
    uu____10948 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____10958  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____10965  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____10972  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____10979  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____10986  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____10993  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____11000  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____11007  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____11014  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____11021  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____11028  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____11035  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____11042  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____11049  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11058  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____11065  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____11081  ->
    let uu____11082 = get_using_facts_from ()  in
    match uu____11082 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____11136  ->
    let uu____11137 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____11137
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____11148  ->
    let uu____11149 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____11149 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____11157 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____11168  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____11175  ->
    let uu____11176 = get_smt ()  in
    match uu____11176 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____11194  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____11201  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____11208  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____11215  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____11222  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____11229  ->
    (get_use_two_phase_tc ()) &&
      (let uu____11231 = lax ()  in Prims.op_Negation uu____11231)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____11239  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____11246  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____11253  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____11260  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____11267  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____11284 =
      let uu____11286 = trace_error ()  in Prims.op_Negation uu____11286  in
    if uu____11284
    then
      (push ();
       (let r =
          try
            (fun uu___97_11301  ->
               match () with
               | () -> let uu____11306 = f ()  in FStar_Util.Inr uu____11306)
              ()
          with | uu___96_11308 -> FStar_Util.Inl uu___96_11308  in
        pop ();
        (match r with
         | FStar_Util.Inr v1 -> v1
         | FStar_Util.Inl ex -> FStar_Exn.raise ex)))
    else (push (); (let retv = f ()  in pop (); retv))
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____11332 = get_extract ()  in
    match uu____11332 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____11347 =
            let uu____11363 = get_no_extract ()  in
            let uu____11367 = get_extract_namespace ()  in
            let uu____11371 = get_extract_module ()  in
            (uu____11363, uu____11367, uu____11371)  in
          match uu____11347 with
          | ([],[],[]) -> ()
          | uu____11396 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____11459,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____11492 -> false  in
          let uu____11504 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____11546  ->
                    match uu____11546 with
                    | (path,uu____11557) -> matches_path m_components path))
             in
          match uu____11504 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____11576,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____11606 = get_extract_namespace ()  in
          match uu____11606 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____11634 = get_extract_module ()  in
          match uu____11634 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____11656 = no_extract m1  in Prims.op_Negation uu____11656)
          &&
          (let uu____11659 =
             let uu____11670 = get_extract_namespace ()  in
             let uu____11674 = get_extract_module ()  in
             (uu____11670, uu____11674)  in
           (match uu____11659 with
            | ([],[]) -> true
            | uu____11694 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  