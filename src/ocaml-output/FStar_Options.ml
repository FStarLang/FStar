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
  fun uu____2212  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____2232  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____2305 =
      let uu____2308 = peek ()  in FStar_Util.smap_try_find uu____2308 s  in
    match uu____2305 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____2321 . Prims.string -> (option_val -> 'Auu____2321) -> 'Auu____2321
  = fun s  -> fun c  -> let uu____2339 = get_option s  in c uu____2339 
let (get_abort_on : unit -> Prims.int) =
  fun uu____2346  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____2355  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____2366  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____2378  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2389  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____2401  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____2410  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2421  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____2435  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____2449  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____2463  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____2474  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2485  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____2497  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____2506  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____2515  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____2526  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____2538  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____2547  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2560  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____2579  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____2593  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____2605  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____2614  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____2623  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2634  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____2646  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____2655  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____2666  -> lookup_opt "include" (as_list as_string) 
let (get_print : unit -> Prims.bool) =
  fun uu____2678  -> lookup_opt "print" as_bool 
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____2687  -> lookup_opt "print_in_place" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____2696  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____2705  -> lookup_opt "initial_ifuel" as_int 
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu____2714  -> lookup_opt "keep_query_captions" as_bool 
let (get_lax : unit -> Prims.bool) =
  fun uu____2723  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____2734  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____2746  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____2755  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____2764  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____2773  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____2782  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____2791  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____2800  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____2809  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____2820  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____2832  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____2841  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____2850  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____2859  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2870  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____2882  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2893  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____2905  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____2914  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____2923  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____2932  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____2941  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____2950  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____2959  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____2968  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____2977  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2988  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____3000  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3011  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____3023  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____3032  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____3041  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____3050  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____3059  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____3068  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____3077  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____3086  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____3095  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____3104  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____3113  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____3122  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____3131  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____3140  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____3149  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____3158  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____3167  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3178  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____3190  ->
    let uu____3191 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____3191
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____3205  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3224  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____3238  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____3252  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____3264  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____3273  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____3284  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____3296  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____3305  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____3314  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____3323  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____3332  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____3341  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____3350  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____3359  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____3368  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____3377  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___86_3386  ->
    match uu___86_3386 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____3407 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____3416 = get_debug_level ()  in
    FStar_All.pipe_right uu____3416
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____3582  ->
    let uu____3583 =
      let uu____3585 = FStar_ST.op_Bang _version  in
      let uu____3608 = FStar_ST.op_Bang _platform  in
      let uu____3631 = FStar_ST.op_Bang _compiler  in
      let uu____3654 = FStar_ST.op_Bang _date  in
      let uu____3677 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____3585
        uu____3608 uu____3631 uu____3654 uu____3677
       in
    FStar_Util.print_string uu____3583
  
let display_usage_aux :
  'Auu____3708 'Auu____3709 .
    ('Auu____3708 * Prims.string * 'Auu____3709 FStar_Getopt.opt_variant *
      Prims.string) Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____3764  ->
         match uu____3764 with
         | (uu____3777,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____3796 =
                      let uu____3798 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____3798  in
                    FStar_Util.print_string uu____3796
                  else
                    (let uu____3803 =
                       let uu____3805 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____3805 doc  in
                     FStar_Util.print_string uu____3803)
              | FStar_Getopt.OneArg (uu____3808,argname) ->
                  if doc = ""
                  then
                    let uu____3823 =
                      let uu____3825 = FStar_Util.colorize_bold flag  in
                      let uu____3827 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____3825 uu____3827
                       in
                    FStar_Util.print_string uu____3823
                  else
                    (let uu____3832 =
                       let uu____3834 = FStar_Util.colorize_bold flag  in
                       let uu____3836 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____3834
                         uu____3836 doc
                        in
                     FStar_Util.print_string uu____3832))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____3871 = o  in
    match uu____3871 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____3913 =
                let uu____3914 = f ()  in set_option name uu____3914  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____3935 = f x  in set_option name uu____3935
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____3962 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____3962  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____3988 =
        let uu____3991 = lookup_opt name as_list'  in
        FStar_List.append uu____3991 [value]  in
      mk_list uu____3988
  
let accumulate_string :
  'Auu____4005 .
    Prims.string -> ('Auu____4005 -> Prims.string) -> 'Auu____4005 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____4030 =
          let uu____4031 =
            let uu____4032 = post_processor value  in mk_string uu____4032
             in
          accumulated_option name uu____4031  in
        set_option name uu____4030
  
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
    match projectee with | Const _0 -> true | uu____4154 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____4175 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____4197 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____4210 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____4234 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____4260 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____4297 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____4348 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____4389 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____4409 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____4436 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____4480 -> true
    | uu____4483 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____4494 -> uu____4494
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___91_4518  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____4520 ->
                      let uu____4522 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____4522 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____4530 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____4530
                  | PathStr uu____4547 -> mk_path str_val
                  | SimpleStr uu____4549 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____4559 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____4576 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____4576
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
            let uu____4596 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____4596
  
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
    | PostProcessed (uu____4666,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____4676,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____4707 = desc_of_opt_type typ  in
      match uu____4707 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____4715  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____4741 =
      let uu____4743 = as_string s  in FStar_String.lowercase uu____4743  in
    mk_string uu____4741
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string)
      Prims.list)
  =
  fun uu____4800  ->
    let uu____4814 =
      let uu____4828 =
        let uu____4842 =
          let uu____4856 =
            let uu____4868 =
              let uu____4869 = mk_bool true  in Const uu____4869  in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____4868,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
             in
          let uu____4876 =
            let uu____4890 =
              let uu____4904 =
                let uu____4916 =
                  let uu____4917 = mk_bool true  in Const uu____4917  in
                (FStar_Getopt.noshort, "cache_off", uu____4916,
                  "Do not read or write any .checked files")
                 in
              let uu____4924 =
                let uu____4938 =
                  let uu____4950 =
                    let uu____4951 = mk_bool true  in Const uu____4951  in
                  (FStar_Getopt.noshort, "cmi", uu____4950,
                    "Inline across module interfaces during extraction (aka. cross-module inlining)")
                   in
                let uu____4958 =
                  let uu____4972 =
                    let uu____4986 =
                      let uu____5000 =
                        let uu____5014 =
                          let uu____5028 =
                            let uu____5042 =
                              let uu____5056 =
                                let uu____5068 =
                                  let uu____5069 = mk_bool true  in
                                  Const uu____5069  in
                                (FStar_Getopt.noshort, "detail_errors",
                                  uu____5068,
                                  "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                 in
                              let uu____5076 =
                                let uu____5090 =
                                  let uu____5102 =
                                    let uu____5103 = mk_bool true  in
                                    Const uu____5103  in
                                  (FStar_Getopt.noshort,
                                    "detail_hint_replay", uu____5102,
                                    "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                   in
                                let uu____5110 =
                                  let uu____5124 =
                                    let uu____5136 =
                                      let uu____5137 = mk_bool true  in
                                      Const uu____5137  in
                                    (FStar_Getopt.noshort, "doc", uu____5136,
                                      "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                     in
                                  let uu____5144 =
                                    let uu____5158 =
                                      let uu____5172 =
                                        let uu____5184 =
                                          let uu____5185 = mk_bool true  in
                                          Const uu____5185  in
                                        (FStar_Getopt.noshort,
                                          "eager_inference", uu____5184,
                                          "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                         in
                                      let uu____5192 =
                                        let uu____5206 =
                                          let uu____5218 =
                                            let uu____5219 = mk_bool true  in
                                            Const uu____5219  in
                                          (FStar_Getopt.noshort,
                                            "eager_subtyping", uu____5218,
                                            "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                           in
                                        let uu____5226 =
                                          let uu____5240 =
                                            let uu____5254 =
                                              let uu____5268 =
                                                let uu____5282 =
                                                  let uu____5294 =
                                                    let uu____5295 =
                                                      mk_bool true  in
                                                    Const uu____5295  in
                                                  (FStar_Getopt.noshort,
                                                    "expose_interfaces",
                                                    uu____5294,
                                                    "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                   in
                                                let uu____5302 =
                                                  let uu____5316 =
                                                    let uu____5328 =
                                                      let uu____5329 =
                                                        mk_bool true  in
                                                      Const uu____5329  in
                                                    (FStar_Getopt.noshort,
                                                      "hide_uvar_nums",
                                                      uu____5328,
                                                      "Don't print unification variable numbers")
                                                     in
                                                  let uu____5336 =
                                                    let uu____5350 =
                                                      let uu____5364 =
                                                        let uu____5376 =
                                                          let uu____5377 =
                                                            mk_bool true  in
                                                          Const uu____5377
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "hint_info",
                                                          uu____5376,
                                                          "Print information regarding hints (deprecated; use --query_stats instead)")
                                                         in
                                                      let uu____5384 =
                                                        let uu____5398 =
                                                          let uu____5410 =
                                                            let uu____5411 =
                                                              mk_bool true
                                                               in
                                                            Const uu____5411
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "in", uu____5410,
                                                            "Legacy interactive mode; reads input from stdin")
                                                           in
                                                        let uu____5418 =
                                                          let uu____5432 =
                                                            let uu____5444 =
                                                              let uu____5445
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____5445
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "ide",
                                                              uu____5444,
                                                              "JSON-based interactive mode for IDEs")
                                                             in
                                                          let uu____5452 =
                                                            let uu____5466 =
                                                              let uu____5480
                                                                =
                                                                let uu____5492
                                                                  =
                                                                  let uu____5493
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                  Const
                                                                    uu____5493
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "print",
                                                                  uu____5492,
                                                                  "Parses and prettyprints the files included on the command line")
                                                                 in
                                                              let uu____5500
                                                                =
                                                                let uu____5514
                                                                  =
                                                                  let uu____5526
                                                                    =
                                                                    let uu____5527
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5527
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "print_in_place",
                                                                    uu____5526,
                                                                    "Parses and prettyprints in place the files included on the command line")
                                                                   in
                                                                let uu____5534
                                                                  =
                                                                  let uu____5548
                                                                    =
                                                                    let uu____5562
                                                                    =
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
                                                                    "lax",
                                                                    uu____5602,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____5610
                                                                    =
                                                                    let uu____5624
                                                                    =
                                                                    let uu____5638
                                                                    =
                                                                    let uu____5650
                                                                    =
                                                                    let uu____5651
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5651
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____5650,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____5658
                                                                    =
                                                                    let uu____5672
                                                                    =
                                                                    let uu____5684
                                                                    =
                                                                    let uu____5685
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5685
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____5684,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____5692
                                                                    =
                                                                    let uu____5706
                                                                    =
                                                                    let uu____5720
                                                                    =
                                                                    let uu____5734
                                                                    =
                                                                    let uu____5748
                                                                    =
                                                                    let uu____5760
                                                                    =
                                                                    let uu____5761
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5761
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____5760,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____5768
                                                                    =
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
                                                                    "no_default_includes",
                                                                    uu____5808,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____5816
                                                                    =
                                                                    let uu____5830
                                                                    =
                                                                    let uu____5844
                                                                    =
                                                                    let uu____5856
                                                                    =
                                                                    let uu____5857
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5857
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____5856,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____5864
                                                                    =
                                                                    let uu____5878
                                                                    =
                                                                    let uu____5890
                                                                    =
                                                                    let uu____5891
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5891
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____5890,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____5898
                                                                    =
                                                                    let uu____5912
                                                                    =
                                                                    let uu____5924
                                                                    =
                                                                    let uu____5925
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5925
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____5924,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____5932
                                                                    =
                                                                    let uu____5946
                                                                    =
                                                                    let uu____5960
                                                                    =
                                                                    let uu____5974
                                                                    =
                                                                    let uu____5986
                                                                    =
                                                                    let uu____5987
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5987
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____5986,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____5994
                                                                    =
                                                                    let uu____6008
                                                                    =
                                                                    let uu____6020
                                                                    =
                                                                    let uu____6021
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6021
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____6020,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____6028
                                                                    =
                                                                    let uu____6042
                                                                    =
                                                                    let uu____6054
                                                                    =
                                                                    let uu____6055
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6055
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____6054,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____6062
                                                                    =
                                                                    let uu____6076
                                                                    =
                                                                    let uu____6088
                                                                    =
                                                                    let uu____6089
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6089
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____6088,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____6096
                                                                    =
                                                                    let uu____6110
                                                                    =
                                                                    let uu____6122
                                                                    =
                                                                    let uu____6123
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6123
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____6122,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____6130
                                                                    =
                                                                    let uu____6144
                                                                    =
                                                                    let uu____6156
                                                                    =
                                                                    let uu____6157
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6157
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____6156,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____6164
                                                                    =
                                                                    let uu____6178
                                                                    =
                                                                    let uu____6190
                                                                    =
                                                                    let uu____6191
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6191
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____6190,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
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
                                                                    "query_stats",
                                                                    uu____6224,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____6232
                                                                    =
                                                                    let uu____6246
                                                                    =
                                                                    let uu____6258
                                                                    =
                                                                    let uu____6259
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6259
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____6258,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____6266
                                                                    =
                                                                    let uu____6280
                                                                    =
                                                                    let uu____6294
                                                                    =
                                                                    let uu____6306
                                                                    =
                                                                    let uu____6307
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6307
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____6306,
                                                                    " ")  in
                                                                    let uu____6314
                                                                    =
                                                                    let uu____6328
                                                                    =
                                                                    let uu____6342
                                                                    =
                                                                    let uu____6356
                                                                    =
                                                                    let uu____6370
                                                                    =
                                                                    let uu____6384
                                                                    =
                                                                    let uu____6396
                                                                    =
                                                                    let uu____6397
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6397
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____6396,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____6404
                                                                    =
                                                                    let uu____6418
                                                                    =
                                                                    let uu____6430
                                                                    =
                                                                    let uu____6431
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6431
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____6430,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
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
                                                                    "tactics_info",
                                                                    uu____6464,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____6472
                                                                    =
                                                                    let uu____6486
                                                                    =
                                                                    let uu____6498
                                                                    =
                                                                    let uu____6499
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6499
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____6498,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____6506
                                                                    =
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
                                                                    "__tactics_nbe",
                                                                    uu____6546,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____6554
                                                                    =
                                                                    let uu____6568
                                                                    =
                                                                    let uu____6582
                                                                    =
                                                                    let uu____6594
                                                                    =
                                                                    let uu____6595
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6595
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____6594,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____6602
                                                                    =
                                                                    let uu____6616
                                                                    =
                                                                    let uu____6628
                                                                    =
                                                                    let uu____6629
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6629
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____6628,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____6636
                                                                    =
                                                                    let uu____6650
                                                                    =
                                                                    let uu____6662
                                                                    =
                                                                    let uu____6663
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6663
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____6662,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____6670
                                                                    =
                                                                    let uu____6684
                                                                    =
                                                                    let uu____6696
                                                                    =
                                                                    let uu____6697
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6697
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____6696,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____6704
                                                                    =
                                                                    let uu____6718
                                                                    =
                                                                    let uu____6730
                                                                    =
                                                                    let uu____6731
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6731
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____6730,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____6738
                                                                    =
                                                                    let uu____6752
                                                                    =
                                                                    let uu____6764
                                                                    =
                                                                    let uu____6765
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6765
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____6764,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
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
                                                                    "use_hints",
                                                                    uu____6798,
                                                                    "Use a previously recorded hints database for proof replay")
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
                                                                    "use_hint_hashes",
                                                                    uu____6832,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____6840
                                                                    =
                                                                    let uu____6854
                                                                    =
                                                                    let uu____6868
                                                                    =
                                                                    let uu____6880
                                                                    =
                                                                    let uu____6881
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6881
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____6880,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____6888
                                                                    =
                                                                    let uu____6902
                                                                    =
                                                                    let uu____6914
                                                                    =
                                                                    let uu____6915
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6915
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____6914,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____6922
                                                                    =
                                                                    let uu____6936
                                                                    =
                                                                    let uu____6950
                                                                    =
                                                                    let uu____6964
                                                                    =
                                                                    let uu____6978
                                                                    =
                                                                    let uu____6990
                                                                    =
                                                                    let uu____6991
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6991
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____6990,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____6998
                                                                    =
                                                                    let uu____7012
                                                                    =
                                                                    let uu____7024
                                                                    =
                                                                    let uu____7025
                                                                    =
                                                                    let uu____7033
                                                                    =
                                                                    let uu____7034
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7034
                                                                     in
                                                                    ((fun
                                                                    uu____7041
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____7033)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7025
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____7024,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____7050
                                                                    =
                                                                    let uu____7064
                                                                    =
                                                                    let uu____7076
                                                                    =
                                                                    let uu____7077
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7077
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____7076,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____7084
                                                                    =
                                                                    let uu____7098
                                                                    =
                                                                    let uu____7112
                                                                    =
                                                                    let uu____7124
                                                                    =
                                                                    let uu____7125
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7125
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____7124,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____7132
                                                                    =
                                                                    let uu____7146
                                                                    =
                                                                    let uu____7160
                                                                    =
                                                                    let uu____7174
                                                                    =
                                                                    let uu____7188
                                                                    =
                                                                    let uu____7202
                                                                    =
                                                                    let uu____7214
                                                                    =
                                                                    let uu____7215
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7215
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____7214,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____7222
                                                                    =
                                                                    let uu____7236
                                                                    =
                                                                    let uu____7248
                                                                    =
                                                                    let uu____7249
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7249
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____7248,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____7256
                                                                    =
                                                                    let uu____7270
                                                                    =
                                                                    let uu____7284
                                                                    =
                                                                    let uu____7298
                                                                    =
                                                                    let uu____7312
                                                                    =
                                                                    let uu____7324
                                                                    =
                                                                    let uu____7325
                                                                    =
                                                                    let uu____7333
                                                                    =
                                                                    let uu____7334
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7334
                                                                     in
                                                                    ((fun
                                                                    uu____7340
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____7333)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7325
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____7324,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____7368
                                                                    =
                                                                    let uu____7382
                                                                    =
                                                                    let uu____7394
                                                                    =
                                                                    let uu____7395
                                                                    =
                                                                    let uu____7403
                                                                    =
                                                                    let uu____7404
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7404
                                                                     in
                                                                    ((fun
                                                                    uu____7410
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____7403)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7395
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____7394,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____7438
                                                                    =
                                                                    let uu____7452
                                                                    =
                                                                    let uu____7464
                                                                    =
                                                                    let uu____7465
                                                                    =
                                                                    let uu____7473
                                                                    =
                                                                    let uu____7474
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7474
                                                                     in
                                                                    ((fun
                                                                    uu____7481
                                                                     ->
                                                                    (
                                                                    let uu____7483
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____7483);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____7473)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7465
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____7464,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____7452]
                                                                     in
                                                                    uu____7382
                                                                    ::
                                                                    uu____7438
                                                                     in
                                                                    uu____7312
                                                                    ::
                                                                    uu____7368
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____7298
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____7284
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____7270
                                                                     in
                                                                    uu____7236
                                                                    ::
                                                                    uu____7256
                                                                     in
                                                                    uu____7202
                                                                    ::
                                                                    uu____7222
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____7188
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____7174
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____7160
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____7146
                                                                     in
                                                                    uu____7112
                                                                    ::
                                                                    uu____7132
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____7098
                                                                     in
                                                                    uu____7064
                                                                    ::
                                                                    uu____7084
                                                                     in
                                                                    uu____7012
                                                                    ::
                                                                    uu____7050
                                                                     in
                                                                    uu____6978
                                                                    ::
                                                                    uu____6998
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____6964
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____6950
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____6936
                                                                     in
                                                                    uu____6902
                                                                    ::
                                                                    uu____6922
                                                                     in
                                                                    uu____6868
                                                                    ::
                                                                    uu____6888
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
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
                                                                    uu____6752
                                                                    ::
                                                                    uu____6772
                                                                     in
                                                                    uu____6718
                                                                    ::
                                                                    uu____6738
                                                                     in
                                                                    uu____6684
                                                                    ::
                                                                    uu____6704
                                                                     in
                                                                    uu____6650
                                                                    ::
                                                                    uu____6670
                                                                     in
                                                                    uu____6616
                                                                    ::
                                                                    uu____6636
                                                                     in
                                                                    uu____6582
                                                                    ::
                                                                    uu____6602
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____6568
                                                                     in
                                                                    uu____6534
                                                                    ::
                                                                    uu____6554
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____6520
                                                                     in
                                                                    uu____6486
                                                                    ::
                                                                    uu____6506
                                                                     in
                                                                    uu____6452
                                                                    ::
                                                                    uu____6472
                                                                     in
                                                                    uu____6418
                                                                    ::
                                                                    uu____6438
                                                                     in
                                                                    uu____6384
                                                                    ::
                                                                    uu____6404
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6370
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6356
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____6342
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____6328
                                                                     in
                                                                    uu____6294
                                                                    ::
                                                                    uu____6314
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____6280
                                                                     in
                                                                    uu____6246
                                                                    ::
                                                                    uu____6266
                                                                     in
                                                                    uu____6212
                                                                    ::
                                                                    uu____6232
                                                                     in
                                                                    uu____6178
                                                                    ::
                                                                    uu____6198
                                                                     in
                                                                    uu____6144
                                                                    ::
                                                                    uu____6164
                                                                     in
                                                                    uu____6110
                                                                    ::
                                                                    uu____6130
                                                                     in
                                                                    uu____6076
                                                                    ::
                                                                    uu____6096
                                                                     in
                                                                    uu____6042
                                                                    ::
                                                                    uu____6062
                                                                     in
                                                                    uu____6008
                                                                    ::
                                                                    uu____6028
                                                                     in
                                                                    uu____5974
                                                                    ::
                                                                    uu____5994
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____5960
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____5946
                                                                     in
                                                                    uu____5912
                                                                    ::
                                                                    uu____5932
                                                                     in
                                                                    uu____5878
                                                                    ::
                                                                    uu____5898
                                                                     in
                                                                    uu____5844
                                                                    ::
                                                                    uu____5864
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____5830
                                                                     in
                                                                    uu____5796
                                                                    ::
                                                                    uu____5816
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____5782
                                                                     in
                                                                    uu____5748
                                                                    ::
                                                                    uu____5768
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____5734
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____5720
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____5706
                                                                     in
                                                                    uu____5672
                                                                    ::
                                                                    uu____5692
                                                                     in
                                                                    uu____5638
                                                                    ::
                                                                    uu____5658
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____5624
                                                                     in
                                                                    uu____5590
                                                                    ::
                                                                    uu____5610
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    "Retain comments in the logged SMT queries (requires --log_queries; default true)")
                                                                    ::
                                                                    uu____5576
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____5562
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (
                                                                    IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try initially (default 2)")
                                                                    ::
                                                                    uu____5548
                                                                   in
                                                                uu____5514 ::
                                                                  uu____5534
                                                                 in
                                                              uu____5480 ::
                                                                uu____5500
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "include",
                                                              (ReverseAccumulated
                                                                 (PathStr
                                                                    "path")),
                                                              "A directory in which to search for files included on the command line")
                                                              :: uu____5466
                                                             in
                                                          uu____5432 ::
                                                            uu____5452
                                                           in
                                                        uu____5398 ::
                                                          uu____5418
                                                         in
                                                      uu____5364 ::
                                                        uu____5384
                                                       in
                                                    (FStar_Getopt.noshort,
                                                      "hint_file",
                                                      (PathStr "path"),
                                                      "Read/write hints to <path> (instead of module-specific hints files)")
                                                      :: uu____5350
                                                     in
                                                  uu____5316 :: uu____5336
                                                   in
                                                uu____5282 :: uu____5302  in
                                              (FStar_Getopt.noshort,
                                                "extract_namespace",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "namespace name")))),
                                                "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                :: uu____5268
                                               in
                                            (FStar_Getopt.noshort,
                                              "extract_module",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "module_name")))),
                                              "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                              :: uu____5254
                                             in
                                          (FStar_Getopt.noshort, "extract",
                                            (Accumulated
                                               (SimpleStr
                                                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                            "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                            :: uu____5240
                                           in
                                        uu____5206 :: uu____5226  in
                                      uu____5172 :: uu____5192  in
                                    (FStar_Getopt.noshort, "dump_module",
                                      (Accumulated (SimpleStr "module_name")),
                                      "") :: uu____5158
                                     in
                                  uu____5124 :: uu____5144  in
                                uu____5090 :: uu____5110  in
                              uu____5056 :: uu____5076  in
                            (FStar_Getopt.noshort, "dep",
                              (EnumStr ["make"; "graph"; "full"; "raw"]),
                              "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                              :: uu____5042
                             in
                          (FStar_Getopt.noshort, "defensive",
                            (EnumStr ["no"; "warn"; "fail"]),
                            "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                            :: uu____5028
                           in
                        (FStar_Getopt.noshort, "debug_level",
                          (Accumulated
                             (OpenEnumStr
                                (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                          "Control the verbosity of debugging info") ::
                          uu____5014
                         in
                      (FStar_Getopt.noshort, "debug",
                        (Accumulated (SimpleStr "module_name")),
                        "Print lots of debugging information while checking module")
                        :: uu____5000
                       in
                    (FStar_Getopt.noshort, "codegen-lib",
                      (Accumulated (SimpleStr "namespace")),
                      "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                      :: uu____4986
                     in
                  (FStar_Getopt.noshort, "codegen",
                    (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                    "Generate code for further compilation to executable code, or build a compiler plugin")
                    :: uu____4972
                   in
                uu____4938 :: uu____4958  in
              uu____4904 :: uu____4924  in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____4890
             in
          uu____4856 :: uu____4876  in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____4842
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____4828
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___87_8987  ->
             match uu___87_8987 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____4814

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____9016  ->
    let uu____9019 = specs_with_types ()  in
    FStar_List.map
      (fun uu____9050  ->
         match uu____9050 with
         | (short,long,typ,doc) ->
             let uu____9072 =
               let uu____9086 = arg_spec_of_opt_type long typ  in
               (short, long, uu____9086, doc)  in
             mk_spec uu____9072) uu____9019

let (settable : Prims.string -> Prims.bool) =
  fun uu___88_9101  ->
    match uu___88_9101 with
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
    | uu____9224 -> false
  
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
       (fun uu____9323  ->
          match uu____9323 with
          | (uu____9338,x,uu____9340,uu____9341) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____9416  ->
          match uu____9416 with
          | (uu____9431,x,uu____9433,uu____9434) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____9450  ->
    let uu____9451 = specs ()  in display_usage_aux uu____9451
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____9483 -> true
    | uu____9486 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____9497 -> uu____9497
  
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
        (fun uu___93_9518  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____9535 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____9535
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____9571  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____9577 =
             let uu____9581 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____9581 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____9577)
       in
    let uu____9638 =
      let uu____9642 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____9642
       in
    (res, uu____9638)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____9684  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____9727 = specs ()  in
       FStar_Getopt.parse_cmdline uu____9727 (fun x  -> ())  in
     (let uu____9734 =
        let uu____9740 =
          let uu____9741 = FStar_List.map mk_string old_verify_module  in
          List uu____9741  in
        ("verify_module", uu____9740)  in
      set_option' uu____9734);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____9760 =
        let uu____9762 =
          let uu____9764 =
            let uu____9766 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____9766  in
          (FStar_String.length f1) - uu____9764  in
        uu____9762 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____9760  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____9779 = get_lax ()  in
    if uu____9779
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____9800 = module_name_of_file_name fn  in should_verify uu____9800
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____9811 = get___temp_no_proj ()  in
    FStar_List.contains m uu____9811
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____9825 = should_verify m  in
    if uu____9825 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____9842  ->
    let uu____9843 = get_no_default_includes ()  in
    if uu____9843
    then get_include ()
    else
      (let lib_paths =
         let uu____9855 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____9855 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____9871 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____9871
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____9898 =
         let uu____9902 = get_include ()  in
         FStar_List.append uu____9902 ["."]  in
       FStar_List.append lib_paths uu____9898)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____9928 = FStar_Util.smap_try_find file_map filename  in
    match uu____9928 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___95_9950  ->
               match () with
               | () ->
                   let uu____9954 = FStar_Util.is_path_absolute filename  in
                   if uu____9954
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____9970 =
                        let uu____9974 = include_path ()  in
                        FStar_List.rev uu____9974  in
                      FStar_Util.find_map uu____9970
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___94_10002 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____10022  ->
    let uu____10023 = get_prims ()  in
    match uu____10023 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____10032 = find_file filename  in
        (match uu____10032 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____10041 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____10041)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____10054  ->
    let uu____10055 = prims ()  in FStar_Util.basename uu____10055
  
let (pervasives : unit -> Prims.string) =
  fun uu____10063  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____10067 = find_file filename  in
    match uu____10067 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____10076 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____10076
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____10086  ->
    let uu____10087 = pervasives ()  in FStar_Util.basename uu____10087
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____10095  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____10099 = find_file filename  in
    match uu____10099 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____10108 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____10108
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____10121 = get_odir ()  in
    match uu____10121 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____10139 = get_cache_dir ()  in
    match uu____10139 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____10148 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____10148
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns  ->
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if FStar_Util.starts_with s "-"
        then
          (let path =
             let uu____10245 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____10245  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____10268 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____10268 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____10364 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____10364 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____10379  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____10388  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10397  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____10404  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____10411  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____10418  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____10428 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____10439 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____10450 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____10461 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____10470  ->
    let uu____10471 = get_codegen ()  in
    FStar_Util.map_opt uu____10471
      (fun uu___89_10477  ->
         match uu___89_10477 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____10483 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____10496  ->
    let uu____10497 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____10497
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____10523  -> let uu____10524 = get_debug ()  in uu____10524 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____10541 = get_debug ()  in
    FStar_All.pipe_right uu____10541 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____10566 = get_debug ()  in
       FStar_All.pipe_right uu____10566 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____10581  ->
    let uu____10582 = get_defensive ()  in uu____10582 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____10592  ->
    let uu____10593 = get_defensive ()  in uu____10593 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10605  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____10612  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____10619  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____10626  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____10636 = get_dump_module ()  in
    FStar_All.pipe_right uu____10636 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____10651  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____10658  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____10668 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____10668
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____10704  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____10712  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____10719  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10728  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____10735  -> get_ide () 
let (print : unit -> Prims.bool) = fun uu____10742  -> get_print () 
let (print_in_place : unit -> Prims.bool) =
  fun uu____10749  -> get_print_in_place () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____10756  ->
    let uu____10757 = get_initial_fuel ()  in
    let uu____10759 = get_max_fuel ()  in Prims.min uu____10757 uu____10759
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____10767  ->
    let uu____10768 = get_initial_ifuel ()  in
    let uu____10770 = get_max_ifuel ()  in Prims.min uu____10768 uu____10770
  
let (interactive : unit -> Prims.bool) =
  fun uu____10778  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____10785  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____10794  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____10801  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____10808  -> get_log_queries () 
let (keep_query_captions : unit -> Prims.bool) =
  fun uu____10815  -> (log_queries ()) && (get_keep_query_captions ()) 
let (log_types : unit -> Prims.bool) = fun uu____10822  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____10829  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____10836  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____10843  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____10850  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____10856  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____10865  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____10872  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____10884 = get_no_extract ()  in
    FStar_All.pipe_right uu____10884
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____10903  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____10910  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____10917  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____10924  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10933  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____10940  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____10947  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____10954  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____10961  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____10968  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____10975  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____10982  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____10989  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____10996  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11005  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____11012  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____11019  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____11026  ->
    let uu____11027 = get_smtencoding_nl_arith_repr ()  in
    uu____11027 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____11037  ->
    let uu____11038 = get_smtencoding_nl_arith_repr ()  in
    uu____11038 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____11048  ->
    let uu____11049 = get_smtencoding_nl_arith_repr ()  in
    uu____11049 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____11059  ->
    let uu____11060 = get_smtencoding_l_arith_repr ()  in
    uu____11060 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____11070  ->
    let uu____11071 = get_smtencoding_l_arith_repr ()  in
    uu____11071 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____11081  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____11088  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____11095  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____11102  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____11109  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____11116  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____11123  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____11130  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____11137  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____11144  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____11151  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____11158  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____11165  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____11172  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11181  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____11188  -> get_use_tactics () 
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu____11204  ->
    let uu____11205 = get_using_facts_from ()  in
    match uu____11205 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____11259  ->
    let uu____11260 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____11260
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____11271  ->
    let uu____11272 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____11272 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____11280 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____11291  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____11298  ->
    let uu____11299 = get_smt ()  in
    match uu____11299 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____11317  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____11324  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____11331  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____11338  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____11345  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____11352  ->
    (get_use_two_phase_tc ()) &&
      (let uu____11354 = lax ()  in Prims.op_Negation uu____11354)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____11362  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____11369  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____11376  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____11383  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____11390  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____11407 =
      let uu____11409 = trace_error ()  in Prims.op_Negation uu____11409  in
    if uu____11407
    then
      (push ();
       (let r =
          try
            (fun uu___97_11424  ->
               match () with
               | () -> let uu____11429 = f ()  in FStar_Util.Inr uu____11429)
              ()
          with | uu___96_11431 -> FStar_Util.Inl uu___96_11431  in
        pop ();
        (match r with
         | FStar_Util.Inr v1 -> v1
         | FStar_Util.Inl ex -> FStar_Exn.raise ex)))
    else (push (); (let retv = f ()  in pop (); retv))
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____11455 = get_extract ()  in
    match uu____11455 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____11470 =
            let uu____11486 = get_no_extract ()  in
            let uu____11490 = get_extract_namespace ()  in
            let uu____11494 = get_extract_module ()  in
            (uu____11486, uu____11490, uu____11494)  in
          match uu____11470 with
          | ([],[],[]) -> ()
          | uu____11519 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____11582,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____11615 -> false  in
          let uu____11627 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____11669  ->
                    match uu____11669 with
                    | (path,uu____11680) -> matches_path m_components path))
             in
          match uu____11627 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____11699,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____11729 = get_extract_namespace ()  in
          match uu____11729 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____11757 = get_extract_module ()  in
          match uu____11757 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____11779 = no_extract m1  in Prims.op_Negation uu____11779)
          &&
          (let uu____11782 =
             let uu____11793 = get_extract_namespace ()  in
             let uu____11797 = get_extract_module ()  in
             (uu____11793, uu____11797)  in
           (match uu____11782 with
            | ([],[]) -> true
            | uu____11817 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  