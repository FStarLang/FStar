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
  
let (snapshot : unit -> (Prims.int * unit)) =
  fun uu____1239  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____1269 = peek ()  in FStar_Util.smap_add uu____1269 k v1
  
let (set_option' : (Prims.string * option_val) -> unit) =
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
  
let (defaults : (Prims.string * option_val) Prims.list) =
  [("__temp_no_proj", (List []));
  ("__temp_fast_implicits", (Bool false));
  ("abort_on", (Int (Prims.parse_int "0")));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
  ("already_cached", Unset);
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
  ("keep_query_captions", (Bool true));
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
  fun uu____2219  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____2239  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____2312 =
      let uu____2315 = peek ()  in FStar_Util.smap_try_find uu____2315 s  in
    match uu____2312 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____2328 . Prims.string -> (option_val -> 'Auu____2328) -> 'Auu____2328
  = fun s  -> fun c  -> let uu____2346 = get_option s  in c uu____2346 
let (get_abort_on : unit -> Prims.int) =
  fun uu____2353  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____2362  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____2373  -> lookup_opt "admit_except" (as_option as_string) 
let (get_already_cached :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2389  ->
    lookup_opt "already_cached" (as_option (as_list as_string))
  
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____2406  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2417  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____2429  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____2438  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2449  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____2463  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____2477  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____2491  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____2502  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2513  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____2525  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____2534  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____2543  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____2554  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____2566  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____2575  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2588  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____2607  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____2621  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____2633  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____2642  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____2651  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2662  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____2674  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____2683  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____2694  -> lookup_opt "include" (as_list as_string) 
let (get_print : unit -> Prims.bool) =
  fun uu____2706  -> lookup_opt "print" as_bool 
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____2715  -> lookup_opt "print_in_place" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____2724  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____2733  -> lookup_opt "initial_ifuel" as_int 
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu____2742  -> lookup_opt "keep_query_captions" as_bool 
let (get_lax : unit -> Prims.bool) =
  fun uu____2751  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____2762  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____2774  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____2783  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____2792  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____2801  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____2810  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____2819  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____2828  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____2837  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____2848  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____2860  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____2869  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____2878  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____2887  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2898  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____2910  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2921  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____2933  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____2942  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____2951  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____2960  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____2969  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____2978  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____2987  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____2996  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____3005  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3016  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____3028  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3039  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____3051  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____3060  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____3069  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____3078  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____3087  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____3096  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____3105  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____3114  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____3123  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____3132  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____3141  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____3150  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____3159  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____3168  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____3177  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____3186  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____3195  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3206  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____3218  ->
    let uu____3219 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____3219
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____3233  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3252  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____3266  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____3280  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____3292  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____3301  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____3312  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____3324  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____3333  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____3342  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____3351  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____3360  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____3369  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____3378  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____3387  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____3396  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____3405  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___86_3414  ->
    match uu___86_3414 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____3435 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____3444 = get_debug_level ()  in
    FStar_All.pipe_right uu____3444
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____3610  ->
    let uu____3611 =
      let uu____3613 = FStar_ST.op_Bang _version  in
      let uu____3636 = FStar_ST.op_Bang _platform  in
      let uu____3659 = FStar_ST.op_Bang _compiler  in
      let uu____3682 = FStar_ST.op_Bang _date  in
      let uu____3705 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____3613
        uu____3636 uu____3659 uu____3682 uu____3705
       in
    FStar_Util.print_string uu____3611
  
let display_usage_aux :
  'Auu____3736 'Auu____3737 .
    ('Auu____3736 * Prims.string * 'Auu____3737 FStar_Getopt.opt_variant *
      Prims.string) Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____3792  ->
         match uu____3792 with
         | (uu____3805,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____3824 =
                      let uu____3826 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____3826  in
                    FStar_Util.print_string uu____3824
                  else
                    (let uu____3831 =
                       let uu____3833 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____3833 doc  in
                     FStar_Util.print_string uu____3831)
              | FStar_Getopt.OneArg (uu____3836,argname) ->
                  if doc = ""
                  then
                    let uu____3851 =
                      let uu____3853 = FStar_Util.colorize_bold flag  in
                      let uu____3855 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____3853 uu____3855
                       in
                    FStar_Util.print_string uu____3851
                  else
                    (let uu____3860 =
                       let uu____3862 = FStar_Util.colorize_bold flag  in
                       let uu____3864 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____3862
                         uu____3864 doc
                        in
                     FStar_Util.print_string uu____3860))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____3899 = o  in
    match uu____3899 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____3941 =
                let uu____3942 = f ()  in set_option name uu____3942  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____3963 = f x  in set_option name uu____3963
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____3990 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____3990  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____4016 =
        let uu____4019 = lookup_opt name as_list'  in
        FStar_List.append uu____4019 [value]  in
      mk_list uu____4016
  
let accumulate_string :
  'Auu____4033 .
    Prims.string -> ('Auu____4033 -> Prims.string) -> 'Auu____4033 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____4058 =
          let uu____4059 =
            let uu____4060 = post_processor value  in mk_string uu____4060
             in
          accumulated_option name uu____4059  in
        set_option name uu____4058
  
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
  | OpenEnumStr of (Prims.string Prims.list * Prims.string) 
  | PostProcessed of ((option_val -> option_val) * opt_type) 
  | Accumulated of opt_type 
  | ReverseAccumulated of opt_type 
  | WithSideEffect of ((unit -> unit) * opt_type) 
let (uu___is_Const : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____4182 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____4203 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____4225 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____4238 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____4262 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____4288 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____4325 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____4376 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____4417 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____4437 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____4464 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____4508 -> true
    | uu____4511 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____4522 -> uu____4522
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___91_4546  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____4548 ->
                      let uu____4550 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____4550 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____4558 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____4558
                  | PathStr uu____4575 -> mk_path str_val
                  | SimpleStr uu____4577 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____4587 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____4604 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____4604
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
            let uu____4624 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____4624
  
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
    | PostProcessed (uu____4694,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____4704,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____4735 = desc_of_opt_type typ  in
      match uu____4735 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____4743  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____4769 =
      let uu____4771 = as_string s  in FStar_String.lowercase uu____4771  in
    mk_string uu____4769
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string)
      Prims.list)
  =
  fun uu____4828  ->
    let uu____4842 =
      let uu____4856 =
        let uu____4870 =
          let uu____4884 =
            let uu____4898 =
              let uu____4910 =
                let uu____4911 = mk_bool true  in Const uu____4911  in
              (FStar_Getopt.noshort, "cache_checked_modules", uu____4910,
                "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
               in
            let uu____4918 =
              let uu____4932 =
                let uu____4946 =
                  let uu____4958 =
                    let uu____4959 = mk_bool true  in Const uu____4959  in
                  (FStar_Getopt.noshort, "cache_off", uu____4958,
                    "Do not read or write any .checked files")
                   in
                let uu____4966 =
                  let uu____4980 =
                    let uu____4992 =
                      let uu____4993 = mk_bool true  in Const uu____4993  in
                    (FStar_Getopt.noshort, "cmi", uu____4992,
                      "Inline across module interfaces during extraction (aka. cross-module inlining)")
                     in
                  let uu____5000 =
                    let uu____5014 =
                      let uu____5028 =
                        let uu____5042 =
                          let uu____5056 =
                            let uu____5070 =
                              let uu____5084 =
                                let uu____5098 =
                                  let uu____5110 =
                                    let uu____5111 = mk_bool true  in
                                    Const uu____5111  in
                                  (FStar_Getopt.noshort, "detail_errors",
                                    uu____5110,
                                    "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                   in
                                let uu____5118 =
                                  let uu____5132 =
                                    let uu____5144 =
                                      let uu____5145 = mk_bool true  in
                                      Const uu____5145  in
                                    (FStar_Getopt.noshort,
                                      "detail_hint_replay", uu____5144,
                                      "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                     in
                                  let uu____5152 =
                                    let uu____5166 =
                                      let uu____5178 =
                                        let uu____5179 = mk_bool true  in
                                        Const uu____5179  in
                                      (FStar_Getopt.noshort, "doc",
                                        uu____5178,
                                        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                       in
                                    let uu____5186 =
                                      let uu____5200 =
                                        let uu____5214 =
                                          let uu____5226 =
                                            let uu____5227 = mk_bool true  in
                                            Const uu____5227  in
                                          (FStar_Getopt.noshort,
                                            "eager_inference", uu____5226,
                                            "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                           in
                                        let uu____5234 =
                                          let uu____5248 =
                                            let uu____5260 =
                                              let uu____5261 = mk_bool true
                                                 in
                                              Const uu____5261  in
                                            (FStar_Getopt.noshort,
                                              "eager_subtyping", uu____5260,
                                              "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                             in
                                          let uu____5268 =
                                            let uu____5282 =
                                              let uu____5296 =
                                                let uu____5310 =
                                                  let uu____5324 =
                                                    let uu____5336 =
                                                      let uu____5337 =
                                                        mk_bool true  in
                                                      Const uu____5337  in
                                                    (FStar_Getopt.noshort,
                                                      "expose_interfaces",
                                                      uu____5336,
                                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                     in
                                                  let uu____5344 =
                                                    let uu____5358 =
                                                      let uu____5370 =
                                                        let uu____5371 =
                                                          mk_bool true  in
                                                        Const uu____5371  in
                                                      (FStar_Getopt.noshort,
                                                        "hide_uvar_nums",
                                                        uu____5370,
                                                        "Don't print unification variable numbers")
                                                       in
                                                    let uu____5378 =
                                                      let uu____5392 =
                                                        let uu____5406 =
                                                          let uu____5418 =
                                                            let uu____5419 =
                                                              mk_bool true
                                                               in
                                                            Const uu____5419
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "hint_info",
                                                            uu____5418,
                                                            "Print information regarding hints (deprecated; use --query_stats instead)")
                                                           in
                                                        let uu____5426 =
                                                          let uu____5440 =
                                                            let uu____5452 =
                                                              let uu____5453
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____5453
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "in",
                                                              uu____5452,
                                                              "Legacy interactive mode; reads input from stdin")
                                                             in
                                                          let uu____5460 =
                                                            let uu____5474 =
                                                              let uu____5486
                                                                =
                                                                let uu____5487
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____5487
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "ide",
                                                                uu____5486,
                                                                "JSON-based interactive mode for IDEs")
                                                               in
                                                            let uu____5494 =
                                                              let uu____5508
                                                                =
                                                                let uu____5522
                                                                  =
                                                                  let uu____5534
                                                                    =
                                                                    let uu____5535
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5535
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "print",
                                                                    uu____5534,
                                                                    "Parses and prettyprints the files included on the command line")
                                                                   in
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
                                                                    "print_in_place",
                                                                    uu____5568,
                                                                    "Parses and prettyprints in place the files included on the command line")
                                                                     in
                                                                  let uu____5576
                                                                    =
                                                                    let uu____5590
                                                                    =
                                                                    let uu____5604
                                                                    =
                                                                    let uu____5618
                                                                    =
                                                                    let uu____5632
                                                                    =
                                                                    let uu____5644
                                                                    =
                                                                    let uu____5645
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5645
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____5644,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____5652
                                                                    =
                                                                    let uu____5666
                                                                    =
                                                                    let uu____5680
                                                                    =
                                                                    let uu____5692
                                                                    =
                                                                    let uu____5693
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5693
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____5692,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
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
                                                                    "log_queries",
                                                                    uu____5726,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____5734
                                                                    =
                                                                    let uu____5748
                                                                    =
                                                                    let uu____5762
                                                                    =
                                                                    let uu____5776
                                                                    =
                                                                    let uu____5790
                                                                    =
                                                                    let uu____5802
                                                                    =
                                                                    let uu____5803
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5803
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____5802,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____5810
                                                                    =
                                                                    let uu____5824
                                                                    =
                                                                    let uu____5838
                                                                    =
                                                                    let uu____5850
                                                                    =
                                                                    let uu____5851
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5851
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____5850,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____5858
                                                                    =
                                                                    let uu____5872
                                                                    =
                                                                    let uu____5886
                                                                    =
                                                                    let uu____5898
                                                                    =
                                                                    let uu____5899
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5899
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____5898,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____5906
                                                                    =
                                                                    let uu____5920
                                                                    =
                                                                    let uu____5932
                                                                    =
                                                                    let uu____5933
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5933
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____5932,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____5940
                                                                    =
                                                                    let uu____5954
                                                                    =
                                                                    let uu____5966
                                                                    =
                                                                    let uu____5967
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5967
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____5966,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____5974
                                                                    =
                                                                    let uu____5988
                                                                    =
                                                                    let uu____6002
                                                                    =
                                                                    let uu____6016
                                                                    =
                                                                    let uu____6028
                                                                    =
                                                                    let uu____6029
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6029
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____6028,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____6036
                                                                    =
                                                                    let uu____6050
                                                                    =
                                                                    let uu____6062
                                                                    =
                                                                    let uu____6063
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6063
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____6062,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____6070
                                                                    =
                                                                    let uu____6084
                                                                    =
                                                                    let uu____6096
                                                                    =
                                                                    let uu____6097
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6097
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____6096,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____6104
                                                                    =
                                                                    let uu____6118
                                                                    =
                                                                    let uu____6130
                                                                    =
                                                                    let uu____6131
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6131
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____6130,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____6138
                                                                    =
                                                                    let uu____6152
                                                                    =
                                                                    let uu____6164
                                                                    =
                                                                    let uu____6165
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6165
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____6164,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____6172
                                                                    =
                                                                    let uu____6186
                                                                    =
                                                                    let uu____6198
                                                                    =
                                                                    let uu____6199
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6199
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____6198,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____6206
                                                                    =
                                                                    let uu____6220
                                                                    =
                                                                    let uu____6232
                                                                    =
                                                                    let uu____6233
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6233
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____6232,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____6240
                                                                    =
                                                                    let uu____6254
                                                                    =
                                                                    let uu____6266
                                                                    =
                                                                    let uu____6267
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6267
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____6266,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____6274
                                                                    =
                                                                    let uu____6288
                                                                    =
                                                                    let uu____6300
                                                                    =
                                                                    let uu____6301
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6301
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____6300,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____6308
                                                                    =
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
                                                                    "silent",
                                                                    uu____6348,
                                                                    "Disable all non-critical output")
                                                                     in
                                                                    let uu____6356
                                                                    =
                                                                    let uu____6370
                                                                    =
                                                                    let uu____6384
                                                                    =
                                                                    let uu____6398
                                                                    =
                                                                    let uu____6412
                                                                    =
                                                                    let uu____6426
                                                                    =
                                                                    let uu____6438
                                                                    =
                                                                    let uu____6439
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6439
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____6438,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____6446
                                                                    =
                                                                    let uu____6460
                                                                    =
                                                                    let uu____6472
                                                                    =
                                                                    let uu____6473
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6473
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____6472,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____6480
                                                                    =
                                                                    let uu____6494
                                                                    =
                                                                    let uu____6506
                                                                    =
                                                                    let uu____6507
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6507
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____6506,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____6514
                                                                    =
                                                                    let uu____6528
                                                                    =
                                                                    let uu____6540
                                                                    =
                                                                    let uu____6541
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6541
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____6540,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____6548
                                                                    =
                                                                    let uu____6562
                                                                    =
                                                                    let uu____6576
                                                                    =
                                                                    let uu____6588
                                                                    =
                                                                    let uu____6589
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6589
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____6588,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____6596
                                                                    =
                                                                    let uu____6610
                                                                    =
                                                                    let uu____6624
                                                                    =
                                                                    let uu____6636
                                                                    =
                                                                    let uu____6637
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6637
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____6636,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____6644
                                                                    =
                                                                    let uu____6658
                                                                    =
                                                                    let uu____6670
                                                                    =
                                                                    let uu____6671
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6671
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____6670,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____6678
                                                                    =
                                                                    let uu____6692
                                                                    =
                                                                    let uu____6704
                                                                    =
                                                                    let uu____6705
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6705
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____6704,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____6712
                                                                    =
                                                                    let uu____6726
                                                                    =
                                                                    let uu____6738
                                                                    =
                                                                    let uu____6739
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6739
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____6738,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____6746
                                                                    =
                                                                    let uu____6760
                                                                    =
                                                                    let uu____6772
                                                                    =
                                                                    let uu____6773
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6773
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____6772,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____6780
                                                                    =
                                                                    let uu____6794
                                                                    =
                                                                    let uu____6806
                                                                    =
                                                                    let uu____6807
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6807
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____6806,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____6814
                                                                    =
                                                                    let uu____6828
                                                                    =
                                                                    let uu____6840
                                                                    =
                                                                    let uu____6841
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6841
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____6840,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____6848
                                                                    =
                                                                    let uu____6862
                                                                    =
                                                                    let uu____6874
                                                                    =
                                                                    let uu____6875
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6875
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____6874,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____6882
                                                                    =
                                                                    let uu____6896
                                                                    =
                                                                    let uu____6910
                                                                    =
                                                                    let uu____6922
                                                                    =
                                                                    let uu____6923
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6923
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____6922,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____6930
                                                                    =
                                                                    let uu____6944
                                                                    =
                                                                    let uu____6956
                                                                    =
                                                                    let uu____6957
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6957
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____6956,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____6964
                                                                    =
                                                                    let uu____6978
                                                                    =
                                                                    let uu____6992
                                                                    =
                                                                    let uu____7006
                                                                    =
                                                                    let uu____7020
                                                                    =
                                                                    let uu____7032
                                                                    =
                                                                    let uu____7033
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7033
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____7032,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____7040
                                                                    =
                                                                    let uu____7054
                                                                    =
                                                                    let uu____7066
                                                                    =
                                                                    let uu____7067
                                                                    =
                                                                    let uu____7075
                                                                    =
                                                                    let uu____7076
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7076
                                                                     in
                                                                    ((fun
                                                                    uu____7083
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____7075)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7067
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____7066,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____7092
                                                                    =
                                                                    let uu____7106
                                                                    =
                                                                    let uu____7118
                                                                    =
                                                                    let uu____7119
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7119
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____7118,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____7126
                                                                    =
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
                                                                    "z3refresh",
                                                                    uu____7166,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
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
                                                                    let uu____7244
                                                                    =
                                                                    let uu____7256
                                                                    =
                                                                    let uu____7257
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7257
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____7256,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____7264
                                                                    =
                                                                    let uu____7278
                                                                    =
                                                                    let uu____7290
                                                                    =
                                                                    let uu____7291
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7291
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____7290,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____7298
                                                                    =
                                                                    let uu____7312
                                                                    =
                                                                    let uu____7326
                                                                    =
                                                                    let uu____7340
                                                                    =
                                                                    let uu____7354
                                                                    =
                                                                    let uu____7366
                                                                    =
                                                                    let uu____7367
                                                                    =
                                                                    let uu____7375
                                                                    =
                                                                    let uu____7376
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7376
                                                                     in
                                                                    ((fun
                                                                    uu____7382
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____7375)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7367
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____7366,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____7410
                                                                    =
                                                                    let uu____7424
                                                                    =
                                                                    let uu____7436
                                                                    =
                                                                    let uu____7437
                                                                    =
                                                                    let uu____7445
                                                                    =
                                                                    let uu____7446
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7446
                                                                     in
                                                                    ((fun
                                                                    uu____7452
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____7445)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7437
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____7436,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____7480
                                                                    =
                                                                    let uu____7494
                                                                    =
                                                                    let uu____7506
                                                                    =
                                                                    let uu____7507
                                                                    =
                                                                    let uu____7515
                                                                    =
                                                                    let uu____7516
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7516
                                                                     in
                                                                    ((fun
                                                                    uu____7523
                                                                     ->
                                                                    (
                                                                    let uu____7525
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____7525);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____7515)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7507
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____7506,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____7494]
                                                                     in
                                                                    uu____7424
                                                                    ::
                                                                    uu____7480
                                                                     in
                                                                    uu____7354
                                                                    ::
                                                                    uu____7410
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____7340
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____7326
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____7312
                                                                     in
                                                                    uu____7278
                                                                    ::
                                                                    uu____7298
                                                                     in
                                                                    uu____7244
                                                                    ::
                                                                    uu____7264
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____7230
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____7216
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____7202
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____7188
                                                                     in
                                                                    uu____7154
                                                                    ::
                                                                    uu____7174
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____7140
                                                                     in
                                                                    uu____7106
                                                                    ::
                                                                    uu____7126
                                                                     in
                                                                    uu____7054
                                                                    ::
                                                                    uu____7092
                                                                     in
                                                                    uu____7020
                                                                    ::
                                                                    uu____7040
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____7006
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____6992
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____6978
                                                                     in
                                                                    uu____6944
                                                                    ::
                                                                    uu____6964
                                                                     in
                                                                    uu____6910
                                                                    ::
                                                                    uu____6930
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____6896
                                                                     in
                                                                    uu____6862
                                                                    ::
                                                                    uu____6882
                                                                     in
                                                                    uu____6828
                                                                    ::
                                                                    uu____6848
                                                                     in
                                                                    uu____6794
                                                                    ::
                                                                    uu____6814
                                                                     in
                                                                    uu____6760
                                                                    ::
                                                                    uu____6780
                                                                     in
                                                                    uu____6726
                                                                    ::
                                                                    uu____6746
                                                                     in
                                                                    uu____6692
                                                                    ::
                                                                    uu____6712
                                                                     in
                                                                    uu____6658
                                                                    ::
                                                                    uu____6678
                                                                     in
                                                                    uu____6624
                                                                    ::
                                                                    uu____6644
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____6610
                                                                     in
                                                                    uu____6576
                                                                    ::
                                                                    uu____6596
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____6562
                                                                     in
                                                                    uu____6528
                                                                    ::
                                                                    uu____6548
                                                                     in
                                                                    uu____6494
                                                                    ::
                                                                    uu____6514
                                                                     in
                                                                    uu____6460
                                                                    ::
                                                                    uu____6480
                                                                     in
                                                                    uu____6426
                                                                    ::
                                                                    uu____6446
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6412
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6398
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____6384
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____6370
                                                                     in
                                                                    uu____6336
                                                                    ::
                                                                    uu____6356
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____6322
                                                                     in
                                                                    uu____6288
                                                                    ::
                                                                    uu____6308
                                                                     in
                                                                    uu____6254
                                                                    ::
                                                                    uu____6274
                                                                     in
                                                                    uu____6220
                                                                    ::
                                                                    uu____6240
                                                                     in
                                                                    uu____6186
                                                                    ::
                                                                    uu____6206
                                                                     in
                                                                    uu____6152
                                                                    ::
                                                                    uu____6172
                                                                     in
                                                                    uu____6118
                                                                    ::
                                                                    uu____6138
                                                                     in
                                                                    uu____6084
                                                                    ::
                                                                    uu____6104
                                                                     in
                                                                    uu____6050
                                                                    ::
                                                                    uu____6070
                                                                     in
                                                                    uu____6016
                                                                    ::
                                                                    uu____6036
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____6002
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____5988
                                                                     in
                                                                    uu____5954
                                                                    ::
                                                                    uu____5974
                                                                     in
                                                                    uu____5920
                                                                    ::
                                                                    uu____5940
                                                                     in
                                                                    uu____5886
                                                                    ::
                                                                    uu____5906
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____5872
                                                                     in
                                                                    uu____5838
                                                                    ::
                                                                    uu____5858
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____5824
                                                                     in
                                                                    uu____5790
                                                                    ::
                                                                    uu____5810
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____5776
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____5762
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____5748
                                                                     in
                                                                    uu____5714
                                                                    ::
                                                                    uu____5734
                                                                     in
                                                                    uu____5680
                                                                    ::
                                                                    uu____5700
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____5666
                                                                     in
                                                                    uu____5632
                                                                    ::
                                                                    uu____5652
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    "Retain comments in the logged SMT queries (requires --log_queries; default true)")
                                                                    ::
                                                                    uu____5618
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____5604
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try initially (default 2)")
                                                                    ::
                                                                    uu____5590
                                                                     in
                                                                  uu____5556
                                                                    ::
                                                                    uu____5576
                                                                   in
                                                                uu____5522 ::
                                                                  uu____5542
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "include",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "path")),
                                                                "A directory in which to search for files included on the command line")
                                                                :: uu____5508
                                                               in
                                                            uu____5474 ::
                                                              uu____5494
                                                             in
                                                          uu____5440 ::
                                                            uu____5460
                                                           in
                                                        uu____5406 ::
                                                          uu____5426
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "hint_file",
                                                        (PathStr "path"),
                                                        "Read/write hints to <path> (instead of module-specific hints files)")
                                                        :: uu____5392
                                                       in
                                                    uu____5358 :: uu____5378
                                                     in
                                                  uu____5324 :: uu____5344
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "extract_namespace",
                                                  (Accumulated
                                                     (PostProcessed
                                                        (pp_lowercase,
                                                          (SimpleStr
                                                             "namespace name")))),
                                                  "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                  :: uu____5310
                                                 in
                                              (FStar_Getopt.noshort,
                                                "extract_module",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "module_name")))),
                                                "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                                :: uu____5296
                                               in
                                            (FStar_Getopt.noshort, "extract",
                                              (Accumulated
                                                 (SimpleStr
                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                              "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                              :: uu____5282
                                             in
                                          uu____5248 :: uu____5268  in
                                        uu____5214 :: uu____5234  in
                                      (FStar_Getopt.noshort, "dump_module",
                                        (Accumulated
                                           (SimpleStr "module_name")), "")
                                        :: uu____5200
                                       in
                                    uu____5166 :: uu____5186  in
                                  uu____5132 :: uu____5152  in
                                uu____5098 :: uu____5118  in
                              (FStar_Getopt.noshort, "dep",
                                (EnumStr ["make"; "graph"; "full"; "raw"]),
                                "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                                :: uu____5084
                               in
                            (FStar_Getopt.noshort, "defensive",
                              (EnumStr ["no"; "warn"; "fail"]),
                              "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                              :: uu____5070
                             in
                          (FStar_Getopt.noshort, "debug_level",
                            (Accumulated
                               (OpenEnumStr
                                  (["Low"; "Medium"; "High"; "Extreme"],
                                    "..."))),
                            "Control the verbosity of debugging info") ::
                            uu____5056
                           in
                        (FStar_Getopt.noshort, "debug",
                          (Accumulated (SimpleStr "module_name")),
                          "Print lots of debugging information while checking module")
                          :: uu____5042
                         in
                      (FStar_Getopt.noshort, "codegen-lib",
                        (Accumulated (SimpleStr "namespace")),
                        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                        :: uu____5028
                       in
                    (FStar_Getopt.noshort, "codegen",
                      (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                      "Generate code for further compilation to executable code, or build a compiler plugin")
                      :: uu____5014
                     in
                  uu____4980 :: uu____5000  in
                uu____4946 :: uu____4966  in
              (FStar_Getopt.noshort, "cache_dir",
                (PostProcessed (pp_validate_dir, (PathStr "dir"))),
                "Read and write .checked and .checked.lax in directory <dir>")
                :: uu____4932
               in
            uu____4898 :: uu____4918  in
          (FStar_Getopt.noshort, "already_cached",
            (Accumulated
               (SimpleStr
                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
            "\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")
            :: uu____4884
           in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____4870
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____4856
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___87_9046  ->
             match uu___87_9046 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____4842

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____9075  ->
    let uu____9078 = specs_with_types ()  in
    FStar_List.map
      (fun uu____9109  ->
         match uu____9109 with
         | (short,long,typ,doc) ->
             let uu____9131 =
               let uu____9145 = arg_spec_of_opt_type long typ  in
               (short, long, uu____9145, doc)  in
             mk_spec uu____9131) uu____9078

let (settable : Prims.string -> Prims.bool) =
  fun uu___88_9160  ->
    match uu___88_9160 with
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
    | uu____9283 -> false
  
let (resettable : Prims.string -> Prims.bool) =
  fun s  ->
    (((settable s) || (s = "z3seed")) || (s = "z3cliopt")) ||
      (s = "using_facts_from")
  
let (all_specs : FStar_Getopt.opt Prims.list) = specs () 
let (all_specs_with_types :
  (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list)
  = specs_with_types () 
let (settable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____9382  ->
          match uu____9382 with
          | (uu____9397,x,uu____9399,uu____9400) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____9475  ->
          match uu____9475 with
          | (uu____9490,x,uu____9492,uu____9493) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____9509  ->
    let uu____9510 = specs ()  in display_usage_aux uu____9510
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____9542 -> true
    | uu____9545 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____9556 -> uu____9556
  
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
        (fun uu___93_9577  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____9594 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____9594
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____9630  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____9636 =
             let uu____9640 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____9640 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____9636)
       in
    let uu____9697 =
      let uu____9701 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____9701
       in
    (res, uu____9697)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____9743  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____9786 = specs ()  in
       FStar_Getopt.parse_cmdline uu____9786 (fun x  -> ())  in
     (let uu____9793 =
        let uu____9799 =
          let uu____9800 = FStar_List.map mk_string old_verify_module  in
          List uu____9800  in
        ("verify_module", uu____9799)  in
      set_option' uu____9793);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____9819 =
        let uu____9821 =
          let uu____9823 =
            let uu____9825 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____9825  in
          (FStar_String.length f1) - uu____9823  in
        uu____9821 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____9819  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____9838 = get_lax ()  in
    if uu____9838
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____9859 = module_name_of_file_name fn  in should_verify uu____9859
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____9870 = get___temp_no_proj ()  in
    FStar_List.contains m uu____9870
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____9884 = should_verify m  in
    if uu____9884 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____9901  ->
    let cache_dir =
      let uu____9906 = get_cache_dir ()  in
      match uu____9906 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some c -> [c]  in
    let uu____9920 = get_no_default_includes ()  in
    if uu____9920
    then
      let uu____9926 = get_include ()  in
      FStar_List.append cache_dir uu____9926
    else
      (let lib_paths =
         let uu____9937 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____9937 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____9953 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____9953
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____9980 =
         let uu____9984 =
           let uu____9988 = get_include ()  in
           FStar_List.append uu____9988 ["."]  in
         FStar_List.append lib_paths uu____9984  in
       FStar_List.append cache_dir uu____9980)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____10015 = FStar_Util.smap_try_find file_map filename  in
    match uu____10015 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___95_10037  ->
               match () with
               | () ->
                   let uu____10041 = FStar_Util.is_path_absolute filename  in
                   if uu____10041
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____10057 =
                        let uu____10061 = include_path ()  in
                        FStar_List.rev uu____10061  in
                      FStar_Util.find_map uu____10057
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___94_10089 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____10109  ->
    let uu____10110 = get_prims ()  in
    match uu____10110 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____10119 = find_file filename  in
        (match uu____10119 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____10128 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____10128)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____10141  ->
    let uu____10142 = prims ()  in FStar_Util.basename uu____10142
  
let (pervasives : unit -> Prims.string) =
  fun uu____10150  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____10154 = find_file filename  in
    match uu____10154 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____10163 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____10163
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____10173  ->
    let uu____10174 = pervasives ()  in FStar_Util.basename uu____10174
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____10182  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____10186 = find_file filename  in
    match uu____10186 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____10195 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____10195
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____10208 = get_odir ()  in
    match uu____10208 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____10226 = get_cache_dir ()  in
    match uu____10226 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____10235 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____10235
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns  ->
    let cache = FStar_Util.smap_create (Prims.parse_int "31")  in
    let with_cache f s =
      let uu____10357 = FStar_Util.smap_try_find cache s  in
      match uu____10357 with
      | FStar_Pervasives_Native.Some s1 -> s1
      | FStar_Pervasives_Native.None  ->
          let res = f s  in (FStar_Util.smap_add cache s res; res)
       in
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if FStar_Util.starts_with s "-"
        then
          (let path =
             let uu____10492 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____10492  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____10515 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              let s1 = FStar_Util.trim_string s  in
              if s1 = ""
              then []
              else
                with_cache
                  (fun s2  ->
                     FStar_All.pipe_right (FStar_Util.split s2 " ")
                       (FStar_List.map parse_one_setting)) s1))
       in
    FStar_All.pipe_right uu____10515 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____10641 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____10641 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____10656  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____10665  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10674  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____10681  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____10688  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____10695  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____10705 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____10716 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____10727 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____10738 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____10747  ->
    let uu____10748 = get_codegen ()  in
    FStar_Util.map_opt uu____10748
      (fun uu___89_10754  ->
         match uu___89_10754 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____10760 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____10773  ->
    let uu____10774 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____10774
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____10800  -> let uu____10801 = get_debug ()  in uu____10801 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____10818 = get_debug ()  in
    FStar_All.pipe_right uu____10818 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____10843 = get_debug ()  in
       FStar_All.pipe_right uu____10843 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____10858  ->
    let uu____10859 = get_defensive ()  in uu____10859 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____10869  ->
    let uu____10870 = get_defensive ()  in uu____10870 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10882  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____10889  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____10896  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____10903  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____10913 = get_dump_module ()  in
    FStar_All.pipe_right uu____10913 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____10928  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____10935  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____10945 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____10945
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____10981  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____10989  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____10996  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11005  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____11012  -> get_ide () 
let (print : unit -> Prims.bool) = fun uu____11019  -> get_print () 
let (print_in_place : unit -> Prims.bool) =
  fun uu____11026  -> get_print_in_place () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____11033  ->
    let uu____11034 = get_initial_fuel ()  in
    let uu____11036 = get_max_fuel ()  in Prims.min uu____11034 uu____11036
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____11044  ->
    let uu____11045 = get_initial_ifuel ()  in
    let uu____11047 = get_max_ifuel ()  in Prims.min uu____11045 uu____11047
  
let (interactive : unit -> Prims.bool) =
  fun uu____11055  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____11062  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____11071  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____11078  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____11085  -> get_log_queries () 
let (keep_query_captions : unit -> Prims.bool) =
  fun uu____11092  -> (log_queries ()) && (get_keep_query_captions ()) 
let (log_types : unit -> Prims.bool) = fun uu____11099  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____11106  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____11113  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____11120  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____11127  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____11133  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____11142  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____11149  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____11161 = get_no_extract ()  in
    FStar_All.pipe_right uu____11161
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____11180  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____11187  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____11194  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____11201  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11210  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____11217  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____11224  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____11231  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____11238  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____11245  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____11252  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____11259  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____11266  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____11273  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11282  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____11289  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____11296  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____11303  ->
    let uu____11304 = get_smtencoding_nl_arith_repr ()  in
    uu____11304 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____11314  ->
    let uu____11315 = get_smtencoding_nl_arith_repr ()  in
    uu____11315 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____11325  ->
    let uu____11326 = get_smtencoding_nl_arith_repr ()  in
    uu____11326 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____11336  ->
    let uu____11337 = get_smtencoding_l_arith_repr ()  in
    uu____11337 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____11347  ->
    let uu____11348 = get_smtencoding_l_arith_repr ()  in
    uu____11348 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____11358  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____11365  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____11372  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____11379  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____11386  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____11393  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____11400  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____11407  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____11414  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____11421  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____11428  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____11435  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____11442  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____11449  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11458  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____11465  -> get_use_tactics () 
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu____11481  ->
    let uu____11482 = get_using_facts_from ()  in
    match uu____11482 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____11536  ->
    let uu____11537 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____11537
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____11548  ->
    let uu____11549 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____11549 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____11557 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____11568  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____11575  ->
    let uu____11576 = get_smt ()  in
    match uu____11576 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____11594  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____11601  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____11608  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____11615  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____11622  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____11629  ->
    (get_use_two_phase_tc ()) &&
      (let uu____11631 = lax ()  in Prims.op_Negation uu____11631)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____11639  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____11646  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____11653  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____11660  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____11667  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____11684 =
      let uu____11686 = trace_error ()  in Prims.op_Negation uu____11686  in
    if uu____11684
    then
      (push ();
       (let r =
          try
            (fun uu___97_11701  ->
               match () with
               | () -> let uu____11706 = f ()  in FStar_Util.Inr uu____11706)
              ()
          with | uu___96_11708 -> FStar_Util.Inl uu___96_11708  in
        pop ();
        (match r with
         | FStar_Util.Inr v1 -> v1
         | FStar_Util.Inl ex -> FStar_Exn.raise ex)))
    else (push (); (let retv = f ()  in pop (); retv))
  
let (module_matches_namespace_filter :
  Prims.string -> Prims.string Prims.list -> Prims.bool) =
  fun m  ->
    fun filter1  ->
      let m1 = FStar_String.lowercase m  in
      let setting = parse_settings filter1  in
      let m_components = path_of_text m1  in
      let rec matches_path m_components1 path =
        match (m_components1, path) with
        | (uu____11789,[]) -> true
        | (m2::ms,p::ps) ->
            (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
        | uu____11822 -> false  in
      let uu____11834 =
        FStar_All.pipe_right setting
          (FStar_Util.try_find
             (fun uu____11876  ->
                match uu____11876 with
                | (path,uu____11887) -> matches_path m_components path))
         in
      match uu____11834 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____11906,flag) -> flag
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____11935 = get_extract ()  in
    match uu____11935 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____11950 =
            let uu____11966 = get_no_extract ()  in
            let uu____11970 = get_extract_namespace ()  in
            let uu____11974 = get_extract_module ()  in
            (uu____11966, uu____11970, uu____11974)  in
          match uu____11950 with
          | ([],[],[]) -> ()
          | uu____11999 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         module_matches_namespace_filter m1 extract_setting)
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____12028 = get_extract_namespace ()  in
          match uu____12028 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____12056 = get_extract_module ()  in
          match uu____12056 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____12078 = no_extract m1  in Prims.op_Negation uu____12078)
          &&
          (let uu____12081 =
             let uu____12092 = get_extract_namespace ()  in
             let uu____12096 = get_extract_module ()  in
             (uu____12092, uu____12096)  in
           (match uu____12081 with
            | ([],[]) -> true
            | uu____12116 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  
let (should_be_already_cached : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____12136 = get_already_cached ()  in
    match uu____12136 with
    | FStar_Pervasives_Native.None  -> false
    | FStar_Pervasives_Native.Some already_cached_setting ->
        module_matches_namespace_filter m already_cached_setting
  