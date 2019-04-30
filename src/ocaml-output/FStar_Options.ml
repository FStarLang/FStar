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
  fun projectee  -> match projectee with | Low  -> true | uu____26 -> false 
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____37 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | High  -> true | uu____48 -> false 
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____59 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____72 -> false
  
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
    match projectee with | Bool _0 -> true | uu____126 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____149 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____172 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____195 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____219 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____243 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _251  -> Bool _251 
let (mk_string : Prims.string -> option_val) = fun _258  -> String _258 
let (mk_path : Prims.string -> option_val) = fun _265  -> Path _265 
let (mk_int : Prims.int -> option_val) = fun _272  -> Int _272 
let (mk_list : option_val Prims.list -> option_val) = fun _280  -> List _280 
type options =
  | Set 
  | Reset 
  | Restore 
let (uu___is_Set : options -> Prims.bool) =
  fun projectee  -> match projectee with | Set  -> true | uu____290 -> false 
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____301 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____312 -> false
  
type error_flag =
  | CFatal 
  | CAlwaysError 
  | CError 
  | CWarning 
  | CSilent 
let (uu___is_CFatal : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CFatal  -> true | uu____323 -> false
  
let (uu___is_CAlwaysError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CAlwaysError  -> true | uu____334 -> false
  
let (uu___is_CError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CError  -> true | uu____345 -> false
  
let (uu___is_CWarning : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CWarning  -> true | uu____356 -> false
  
let (uu___is_CSilent : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CSilent  -> true | uu____367 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____381  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____408  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____436  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___0_465  ->
    match uu___0_465 with
    | Bool b -> b
    | uu____469 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___1_478  ->
    match uu___1_478 with
    | Int b -> b
    | uu____482 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___2_491  ->
    match uu___2_491 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____497 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___3_507  ->
    match uu___3_507 with
    | List ts -> ts
    | uu____513 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____524 .
    (option_val -> 'Auu____524) -> option_val -> 'Auu____524 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____542 = as_list' x  in
      FStar_All.pipe_right uu____542 (FStar_List.map as_t)
  
let as_option :
  'Auu____556 .
    (option_val -> 'Auu____556) ->
      option_val -> 'Auu____556 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___4_571  ->
      match uu___4_571 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____575 = as_t v1  in FStar_Pervasives_Native.Some uu____575
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___5_584  ->
    match uu___5_584 with
    | List ls ->
        let uu____591 =
          FStar_List.map
            (fun l  ->
               let uu____603 = as_string l  in FStar_Util.split uu____603 ",")
            ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____591
    | uu____615 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let copy_optionstate :
  'Auu____627 . 'Auu____627 FStar_Util.smap -> 'Auu____627 FStar_Util.smap =
  fun m  -> FStar_Util.smap_copy m 
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (internal_peek : unit -> optionstate) =
  fun uu____657  ->
    let uu____658 =
      let uu____661 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____661  in
    FStar_List.hd uu____658
  
let (peek : unit -> optionstate) = fun uu____700  -> internal_peek () 
let (pop : unit -> unit) =
  fun uu____706  ->
    let uu____707 = FStar_ST.op_Bang fstar_options  in
    match uu____707 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____742::[] -> failwith "TOO MANY POPS!"
    | uu____750::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____792  ->
    let uu____793 =
      let uu____798 =
        let uu____801 =
          let uu____804 = FStar_ST.op_Bang fstar_options  in
          FStar_List.hd uu____804  in
        FStar_List.map copy_optionstate uu____801  in
      let uu____838 = FStar_ST.op_Bang fstar_options  in uu____798 ::
        uu____838
       in
    FStar_ST.op_Colon_Equals fstar_options uu____793
  
let (internal_pop : unit -> Prims.bool) =
  fun uu____905  ->
    let curstack =
      let uu____909 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____909  in
    match curstack with
    | [] -> failwith "impossible: empty current option stack"
    | uu____946::[] -> false
    | uu____948::tl1 ->
        ((let uu____953 =
            let uu____958 =
              let uu____963 = FStar_ST.op_Bang fstar_options  in
              FStar_List.tl uu____963  in
            tl1 :: uu____958  in
          FStar_ST.op_Colon_Equals fstar_options uu____953);
         true)
  
let (internal_push : unit -> unit) =
  fun uu____1032  ->
    let curstack =
      let uu____1036 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____1036  in
    let stack' =
      let uu____1073 =
        let uu____1074 = FStar_List.hd curstack  in
        copy_optionstate uu____1074  in
      uu____1073 :: curstack  in
    let uu____1077 =
      let uu____1082 =
        let uu____1087 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____1087  in
      stack' :: uu____1082  in
    FStar_ST.op_Colon_Equals fstar_options uu____1077
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____1156 = FStar_ST.op_Bang fstar_options  in
    match uu____1156 with
    | [] -> failwith "set on empty option stack"
    | []::uu____1191 -> failwith "set on empty current option stack"
    | (uu____1199::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
  
let (snapshot : unit -> (Prims.int * unit)) =
  fun uu____1249  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____1279 = peek ()  in FStar_Util.smap_add uu____1279 k v1
  
let (set_option' : (Prims.string * option_val) -> unit) =
  fun uu____1292  -> match uu____1292 with | (k,v1) -> set_option k v1 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____1320 =
      let uu____1324 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____1324
       in
    FStar_ST.op_Colon_Equals light_off_files uu____1320
  
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
  ("profile", (Bool false));
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
  ("smtencoding.valid_intro", (Bool true));
  ("smtencoding.valid_elim", (Bool false));
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
  ("warn_error", (List []));
  ("use_extracted_interfaces", (Bool false));
  ("use_nbe", (Bool false))] 
let (parse_warn_error_set_get :
  (((Prims.string -> error_flag Prims.list) -> unit) *
    (unit -> Prims.string -> error_flag Prims.list)))
  =
  let r = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let set1 f =
    let uu____2301 = FStar_ST.op_Bang r  in
    match uu____2301 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some f)
    | uu____2392 -> failwith "Multiple initialization of FStar.Options"  in
  let get1 uu____2413 =
    let uu____2414 = FStar_ST.op_Bang r  in
    match uu____2414 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        failwith "FStar.Options is improperly initialized"
     in
  (set1, get1) 
let (initialize_parse_warn_error :
  (Prims.string -> error_flag Prims.list) -> unit) =
  fun f  -> FStar_Pervasives_Native.fst parse_warn_error_set_get f 
let (parse_warn_error : Prims.string -> error_flag Prims.list) =
  fun s  ->
    let uu____2553 = FStar_Pervasives_Native.snd parse_warn_error_set_get ()
       in
    uu____2553 s
  
let (init : unit -> unit) =
  fun uu____2584  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____2604  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____2677 =
      let uu____2680 = peek ()  in FStar_Util.smap_try_find uu____2680 s  in
    match uu____2677 with
    | FStar_Pervasives_Native.None  ->
        let uu____2683 =
          let uu____2685 = FStar_String.op_Hat s " not found"  in
          FStar_String.op_Hat "Impossible: option " uu____2685  in
        failwith uu____2683
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____2697 . Prims.string -> (option_val -> 'Auu____2697) -> 'Auu____2697
  = fun s  -> fun c  -> let uu____2715 = get_option s  in c uu____2715 
let (get_abort_on : unit -> Prims.int) =
  fun uu____2722  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____2731  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____2742  -> lookup_opt "admit_except" (as_option as_string) 
let (get_already_cached :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2758  ->
    lookup_opt "already_cached" (as_option (as_list as_string))
  
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____2775  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2786  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____2798  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____2807  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2818  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____2832  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____2846  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____2860  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____2871  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2882  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____2894  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____2903  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____2912  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____2923  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____2935  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____2944  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2957  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____2976  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____2990  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____3002  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____3011  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____3020  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3031  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____3043  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____3052  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____3063  -> lookup_opt "include" (as_list as_string) 
let (get_print : unit -> Prims.bool) =
  fun uu____3075  -> lookup_opt "print" as_bool 
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____3084  -> lookup_opt "print_in_place" as_bool 
let (get_profile : unit -> Prims.bool) =
  fun uu____3093  -> lookup_opt "profile" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____3102  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____3111  -> lookup_opt "initial_ifuel" as_int 
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu____3120  -> lookup_opt "keep_query_captions" as_bool 
let (get_lax : unit -> Prims.bool) =
  fun uu____3129  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____3140  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____3152  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____3161  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____3170  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____3179  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____3188  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____3197  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____3206  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____3215  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____3226  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____3238  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____3247  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____3256  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____3265  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3276  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____3288  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3299  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____3311  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____3320  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____3329  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____3338  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____3347  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____3356  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____3365  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____3374  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____3383  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3394  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____3406  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3417  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____3429  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____3438  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____3447  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_smtencoding_valid_intro : unit -> Prims.bool) =
  fun uu____3456  -> lookup_opt "smtencoding.valid_intro" as_bool 
let (get_smtencoding_valid_elim : unit -> Prims.bool) =
  fun uu____3465  -> lookup_opt "smtencoding.valid_elim" as_bool 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____3474  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____3483  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____3492  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____3501  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____3510  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____3519  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____3528  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____3537  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____3546  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____3555  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____3564  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____3573  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____3582  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____3591  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3602  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____3614  ->
    let uu____3615 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____3615
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____3629  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3648  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____3662  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____3676  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____3688  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____3697  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____3708  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____3720  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____3729  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____3738  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____3747  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____3756  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____3765  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____3774  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string Prims.list) =
  fun uu____3785  -> lookup_opt "warn_error" (as_list as_string) 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____3797  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____3806  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___6_3815  ->
    match uu___6_3815 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____3836 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____3845 = get_debug_level ()  in
    FStar_All.pipe_right uu____3845
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "<not set>" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____3901  ->
    let uu____3902 =
      let uu____3904 = FStar_ST.op_Bang _version  in
      let uu____3927 = FStar_ST.op_Bang _platform  in
      let uu____3950 = FStar_ST.op_Bang _compiler  in
      let uu____3973 = FStar_ST.op_Bang _date  in
      let uu____3996 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____3904
        uu____3927 uu____3950 uu____3973 uu____3996
       in
    FStar_Util.print_string uu____3902
  
let display_usage_aux :
  'Auu____4027 'Auu____4028 .
    ('Auu____4027 * Prims.string * 'Auu____4028 FStar_Getopt.opt_variant *
      Prims.string) Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____4083  ->
         match uu____4083 with
         | (uu____4096,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____4115 =
                      let uu____4117 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____4117  in
                    FStar_Util.print_string uu____4115
                  else
                    (let uu____4122 =
                       let uu____4124 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____4124 doc  in
                     FStar_Util.print_string uu____4122)
              | FStar_Getopt.OneArg (uu____4127,argname) ->
                  if doc = ""
                  then
                    let uu____4142 =
                      let uu____4144 = FStar_Util.colorize_bold flag  in
                      let uu____4146 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____4144 uu____4146
                       in
                    FStar_Util.print_string uu____4142
                  else
                    (let uu____4151 =
                       let uu____4153 = FStar_Util.colorize_bold flag  in
                       let uu____4155 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____4153
                         uu____4155 doc
                        in
                     FStar_Util.print_string uu____4151))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____4190 = o  in
    match uu____4190 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____4232 =
                let uu____4233 = f ()  in set_option name uu____4233  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____4254 = f x  in set_option name uu____4254
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____4281 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____4281  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____4310 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____4310  in
      mk_list (FStar_List.append prev_values [value])
  
let accumulate_string :
  'Auu____4332 .
    Prims.string -> ('Auu____4332 -> Prims.string) -> 'Auu____4332 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____4357 =
          let uu____4358 =
            let uu____4359 = post_processor value  in mk_string uu____4359
             in
          accumulated_option name uu____4358  in
        set_option name uu____4357
  
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
    match projectee with | Const _0 -> true | uu____4481 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____4501 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____4522 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____4535 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____4558 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____4583 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____4619 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____4669 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____4709 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____4728 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____4754 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____4797 -> true
    | uu____4800 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____4810 -> uu____4810
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___294_4834  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____4836 ->
                      let uu____4838 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____4838 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____4846 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____4846
                  | PathStr uu____4863 -> mk_path str_val
                  | SimpleStr uu____4865 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____4875 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____4892 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____4892
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
            let uu____4912 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____4912
  
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ  ->
    let desc_of_enum cases =
      let uu____4942 =
        let uu____4944 =
          FStar_String.op_Hat (FStar_String.concat "|" cases) "]"  in
        FStar_String.op_Hat "[" uu____4944  in
      FStar_Pervasives_Native.Some uu____4942  in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____4986,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____4996,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____5027 = desc_of_opt_type typ  in
      match uu____5027 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____5035  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____5061 =
      let uu____5063 = as_string s  in FStar_String.lowercase uu____5063  in
    mk_string uu____5061
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string)
      Prims.list)
  =
  fun uu____5098  ->
    let uu____5112 =
      let uu____5126 =
        let uu____5140 =
          let uu____5154 =
            let uu____5168 =
              let uu____5180 =
                let uu____5181 = mk_bool true  in Const uu____5181  in
              (FStar_Getopt.noshort, "cache_checked_modules", uu____5180,
                "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
               in
            let uu____5188 =
              let uu____5202 =
                let uu____5216 =
                  let uu____5228 =
                    let uu____5229 = mk_bool true  in Const uu____5229  in
                  (FStar_Getopt.noshort, "cache_off", uu____5228,
                    "Do not read or write any .checked files")
                   in
                let uu____5236 =
                  let uu____5250 =
                    let uu____5262 =
                      let uu____5263 = mk_bool true  in Const uu____5263  in
                    (FStar_Getopt.noshort, "cmi", uu____5262,
                      "Inline across module interfaces during extraction (aka. cross-module inlining)")
                     in
                  let uu____5270 =
                    let uu____5284 =
                      let uu____5298 =
                        let uu____5312 =
                          let uu____5326 =
                            let uu____5340 =
                              let uu____5354 =
                                let uu____5368 =
                                  let uu____5380 =
                                    let uu____5381 = mk_bool true  in
                                    Const uu____5381  in
                                  (FStar_Getopt.noshort, "detail_errors",
                                    uu____5380,
                                    "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                   in
                                let uu____5388 =
                                  let uu____5402 =
                                    let uu____5414 =
                                      let uu____5415 = mk_bool true  in
                                      Const uu____5415  in
                                    (FStar_Getopt.noshort,
                                      "detail_hint_replay", uu____5414,
                                      "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                     in
                                  let uu____5422 =
                                    let uu____5436 =
                                      let uu____5448 =
                                        let uu____5449 = mk_bool true  in
                                        Const uu____5449  in
                                      (FStar_Getopt.noshort, "doc",
                                        uu____5448,
                                        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                       in
                                    let uu____5456 =
                                      let uu____5470 =
                                        let uu____5484 =
                                          let uu____5496 =
                                            let uu____5497 = mk_bool true  in
                                            Const uu____5497  in
                                          (FStar_Getopt.noshort,
                                            "eager_inference", uu____5496,
                                            "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                           in
                                        let uu____5504 =
                                          let uu____5518 =
                                            let uu____5530 =
                                              let uu____5531 = mk_bool true
                                                 in
                                              Const uu____5531  in
                                            (FStar_Getopt.noshort,
                                              "eager_subtyping", uu____5530,
                                              "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                             in
                                          let uu____5538 =
                                            let uu____5552 =
                                              let uu____5566 =
                                                let uu____5580 =
                                                  let uu____5594 =
                                                    let uu____5606 =
                                                      let uu____5607 =
                                                        mk_bool true  in
                                                      Const uu____5607  in
                                                    (FStar_Getopt.noshort,
                                                      "expose_interfaces",
                                                      uu____5606,
                                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                     in
                                                  let uu____5614 =
                                                    let uu____5628 =
                                                      let uu____5640 =
                                                        let uu____5641 =
                                                          mk_bool true  in
                                                        Const uu____5641  in
                                                      (FStar_Getopt.noshort,
                                                        "hide_uvar_nums",
                                                        uu____5640,
                                                        "Don't print unification variable numbers")
                                                       in
                                                    let uu____5648 =
                                                      let uu____5662 =
                                                        let uu____5676 =
                                                          let uu____5688 =
                                                            let uu____5689 =
                                                              mk_bool true
                                                               in
                                                            Const uu____5689
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "hint_info",
                                                            uu____5688,
                                                            "Print information regarding hints (deprecated; use --query_stats instead)")
                                                           in
                                                        let uu____5696 =
                                                          let uu____5710 =
                                                            let uu____5722 =
                                                              let uu____5723
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____5723
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "in",
                                                              uu____5722,
                                                              "Legacy interactive mode; reads input from stdin")
                                                             in
                                                          let uu____5730 =
                                                            let uu____5744 =
                                                              let uu____5756
                                                                =
                                                                let uu____5757
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____5757
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "ide",
                                                                uu____5756,
                                                                "JSON-based interactive mode for IDEs")
                                                               in
                                                            let uu____5764 =
                                                              let uu____5778
                                                                =
                                                                let uu____5792
                                                                  =
                                                                  let uu____5804
                                                                    =
                                                                    let uu____5805
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5805
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "print",
                                                                    uu____5804,
                                                                    "Parses and prettyprints the files included on the command line")
                                                                   in
                                                                let uu____5812
                                                                  =
                                                                  let uu____5826
                                                                    =
                                                                    let uu____5838
                                                                    =
                                                                    let uu____5839
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5839
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_in_place",
                                                                    uu____5838,
                                                                    "Parses and prettyprints in place the files included on the command line")
                                                                     in
                                                                  let uu____5846
                                                                    =
                                                                    let uu____5860
                                                                    =
                                                                    let uu____5872
                                                                    =
                                                                    let uu____5873
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5873
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "profile",
                                                                    uu____5872,
                                                                    "Prints timing information for various operations in the compiler")
                                                                     in
                                                                    let uu____5880
                                                                    =
                                                                    let uu____5894
                                                                    =
                                                                    let uu____5908
                                                                    =
                                                                    let uu____5922
                                                                    =
                                                                    let uu____5936
                                                                    =
                                                                    let uu____5948
                                                                    =
                                                                    let uu____5949
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5949
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____5948,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____5956
                                                                    =
                                                                    let uu____5970
                                                                    =
                                                                    let uu____5984
                                                                    =
                                                                    let uu____5996
                                                                    =
                                                                    let uu____5997
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5997
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____5996,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____6004
                                                                    =
                                                                    let uu____6018
                                                                    =
                                                                    let uu____6030
                                                                    =
                                                                    let uu____6031
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6031
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____6030,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____6038
                                                                    =
                                                                    let uu____6052
                                                                    =
                                                                    let uu____6066
                                                                    =
                                                                    let uu____6080
                                                                    =
                                                                    let uu____6094
                                                                    =
                                                                    let uu____6106
                                                                    =
                                                                    let uu____6107
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6107
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____6106,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____6114
                                                                    =
                                                                    let uu____6128
                                                                    =
                                                                    let uu____6142
                                                                    =
                                                                    let uu____6154
                                                                    =
                                                                    let uu____6155
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6155
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____6154,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____6162
                                                                    =
                                                                    let uu____6176
                                                                    =
                                                                    let uu____6190
                                                                    =
                                                                    let uu____6202
                                                                    =
                                                                    let uu____6203
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6203
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____6202,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____6210
                                                                    =
                                                                    let uu____6224
                                                                    =
                                                                    let uu____6236
                                                                    =
                                                                    let uu____6237
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6237
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____6236,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____6244
                                                                    =
                                                                    let uu____6258
                                                                    =
                                                                    let uu____6270
                                                                    =
                                                                    let uu____6271
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6271
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____6270,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____6278
                                                                    =
                                                                    let uu____6292
                                                                    =
                                                                    let uu____6306
                                                                    =
                                                                    let uu____6320
                                                                    =
                                                                    let uu____6332
                                                                    =
                                                                    let uu____6333
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6333
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____6332,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____6340
                                                                    =
                                                                    let uu____6354
                                                                    =
                                                                    let uu____6366
                                                                    =
                                                                    let uu____6367
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6367
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____6366,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____6374
                                                                    =
                                                                    let uu____6388
                                                                    =
                                                                    let uu____6400
                                                                    =
                                                                    let uu____6401
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6401
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____6400,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____6408
                                                                    =
                                                                    let uu____6422
                                                                    =
                                                                    let uu____6434
                                                                    =
                                                                    let uu____6435
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6435
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____6434,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____6442
                                                                    =
                                                                    let uu____6456
                                                                    =
                                                                    let uu____6468
                                                                    =
                                                                    let uu____6469
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6469
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____6468,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____6476
                                                                    =
                                                                    let uu____6490
                                                                    =
                                                                    let uu____6502
                                                                    =
                                                                    let uu____6503
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6503
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____6502,
                                                                    "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)")
                                                                     in
                                                                    let uu____6510
                                                                    =
                                                                    let uu____6524
                                                                    =
                                                                    let uu____6536
                                                                    =
                                                                    let uu____6537
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6537
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____6536,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____6544
                                                                    =
                                                                    let uu____6558
                                                                    =
                                                                    let uu____6570
                                                                    =
                                                                    let uu____6571
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6571
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____6570,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____6578
                                                                    =
                                                                    let uu____6592
                                                                    =
                                                                    let uu____6604
                                                                    =
                                                                    let uu____6605
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6605
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____6604,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____6612
                                                                    =
                                                                    let uu____6626
                                                                    =
                                                                    let uu____6640
                                                                    =
                                                                    let uu____6652
                                                                    =
                                                                    let uu____6653
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6653
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____6652,
                                                                    "Disable all non-critical output")
                                                                     in
                                                                    let uu____6660
                                                                    =
                                                                    let uu____6674
                                                                    =
                                                                    let uu____6688
                                                                    =
                                                                    let uu____6702
                                                                    =
                                                                    let uu____6716
                                                                    =
                                                                    let uu____6730
                                                                    =
                                                                    let uu____6744
                                                                    =
                                                                    let uu____6758
                                                                    =
                                                                    let uu____6770
                                                                    =
                                                                    let uu____6771
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6771
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____6770,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____6778
                                                                    =
                                                                    let uu____6792
                                                                    =
                                                                    let uu____6804
                                                                    =
                                                                    let uu____6805
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6805
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____6804,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____6812
                                                                    =
                                                                    let uu____6826
                                                                    =
                                                                    let uu____6838
                                                                    =
                                                                    let uu____6839
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6839
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____6838,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____6846
                                                                    =
                                                                    let uu____6860
                                                                    =
                                                                    let uu____6872
                                                                    =
                                                                    let uu____6873
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6873
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____6872,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____6880
                                                                    =
                                                                    let uu____6894
                                                                    =
                                                                    let uu____6908
                                                                    =
                                                                    let uu____6920
                                                                    =
                                                                    let uu____6921
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6921
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____6920,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____6928
                                                                    =
                                                                    let uu____6942
                                                                    =
                                                                    let uu____6956
                                                                    =
                                                                    let uu____6968
                                                                    =
                                                                    let uu____6969
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6969
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____6968,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____6976
                                                                    =
                                                                    let uu____6990
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
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____7002,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____7010
                                                                    =
                                                                    let uu____7024
                                                                    =
                                                                    let uu____7036
                                                                    =
                                                                    let uu____7037
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7037
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____7036,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____7044
                                                                    =
                                                                    let uu____7058
                                                                    =
                                                                    let uu____7070
                                                                    =
                                                                    let uu____7071
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7071
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____7070,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____7078
                                                                    =
                                                                    let uu____7092
                                                                    =
                                                                    let uu____7104
                                                                    =
                                                                    let uu____7105
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7105
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____7104,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____7112
                                                                    =
                                                                    let uu____7126
                                                                    =
                                                                    let uu____7138
                                                                    =
                                                                    let uu____7139
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7139
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____7138,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____7146
                                                                    =
                                                                    let uu____7160
                                                                    =
                                                                    let uu____7172
                                                                    =
                                                                    let uu____7173
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7173
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____7172,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____7180
                                                                    =
                                                                    let uu____7194
                                                                    =
                                                                    let uu____7206
                                                                    =
                                                                    let uu____7207
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7207
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____7206,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____7214
                                                                    =
                                                                    let uu____7228
                                                                    =
                                                                    let uu____7242
                                                                    =
                                                                    let uu____7254
                                                                    =
                                                                    let uu____7255
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7255
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____7254,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____7262
                                                                    =
                                                                    let uu____7276
                                                                    =
                                                                    let uu____7288
                                                                    =
                                                                    let uu____7289
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7289
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____7288,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____7296
                                                                    =
                                                                    let uu____7310
                                                                    =
                                                                    let uu____7324
                                                                    =
                                                                    let uu____7338
                                                                    =
                                                                    let uu____7352
                                                                    =
                                                                    let uu____7364
                                                                    =
                                                                    let uu____7365
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7365
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____7364,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____7372
                                                                    =
                                                                    let uu____7386
                                                                    =
                                                                    let uu____7398
                                                                    =
                                                                    let uu____7399
                                                                    =
                                                                    let uu____7407
                                                                    =
                                                                    let uu____7408
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7408
                                                                     in
                                                                    ((fun
                                                                    uu____7415
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____7407)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7399
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____7398,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____7424
                                                                    =
                                                                    let uu____7438
                                                                    =
                                                                    let uu____7450
                                                                    =
                                                                    let uu____7451
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7451
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____7450,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____7458
                                                                    =
                                                                    let uu____7472
                                                                    =
                                                                    let uu____7486
                                                                    =
                                                                    let uu____7498
                                                                    =
                                                                    let uu____7499
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7499
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____7498,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____7506
                                                                    =
                                                                    let uu____7520
                                                                    =
                                                                    let uu____7534
                                                                    =
                                                                    let uu____7548
                                                                    =
                                                                    let uu____7562
                                                                    =
                                                                    let uu____7576
                                                                    =
                                                                    let uu____7588
                                                                    =
                                                                    let uu____7589
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7589
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____7588,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____7596
                                                                    =
                                                                    let uu____7610
                                                                    =
                                                                    let uu____7622
                                                                    =
                                                                    let uu____7623
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7623
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____7622,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____7630
                                                                    =
                                                                    let uu____7644
                                                                    =
                                                                    let uu____7658
                                                                    =
                                                                    let uu____7672
                                                                    =
                                                                    let uu____7686
                                                                    =
                                                                    let uu____7698
                                                                    =
                                                                    let uu____7699
                                                                    =
                                                                    let uu____7707
                                                                    =
                                                                    let uu____7708
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7708
                                                                     in
                                                                    ((fun
                                                                    uu____7714
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____7707)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7699
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____7698,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____7742
                                                                    =
                                                                    let uu____7756
                                                                    =
                                                                    let uu____7768
                                                                    =
                                                                    let uu____7769
                                                                    =
                                                                    let uu____7777
                                                                    =
                                                                    let uu____7778
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7778
                                                                     in
                                                                    ((fun
                                                                    uu____7784
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____7777)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7769
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____7768,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____7812
                                                                    =
                                                                    let uu____7826
                                                                    =
                                                                    let uu____7838
                                                                    =
                                                                    let uu____7839
                                                                    =
                                                                    let uu____7847
                                                                    =
                                                                    let uu____7848
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7848
                                                                     in
                                                                    ((fun
                                                                    uu____7855
                                                                     ->
                                                                    (
                                                                    let uu____7857
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____7857);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____7847)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7839
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____7838,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____7826]
                                                                     in
                                                                    uu____7756
                                                                    ::
                                                                    uu____7812
                                                                     in
                                                                    uu____7686
                                                                    ::
                                                                    uu____7742
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____7672
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____7658
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "")),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____7644
                                                                     in
                                                                    uu____7610
                                                                    ::
                                                                    uu____7630
                                                                     in
                                                                    uu____7576
                                                                    ::
                                                                    uu____7596
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____7562
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____7548
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____7534
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____7520
                                                                     in
                                                                    uu____7486
                                                                    ::
                                                                    uu____7506
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____7472
                                                                     in
                                                                    uu____7438
                                                                    ::
                                                                    uu____7458
                                                                     in
                                                                    uu____7386
                                                                    ::
                                                                    uu____7424
                                                                     in
                                                                    uu____7352
                                                                    ::
                                                                    uu____7372
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____7338
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____7324
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____7310
                                                                     in
                                                                    uu____7276
                                                                    ::
                                                                    uu____7296
                                                                     in
                                                                    uu____7242
                                                                    ::
                                                                    uu____7262
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____7228
                                                                     in
                                                                    uu____7194
                                                                    ::
                                                                    uu____7214
                                                                     in
                                                                    uu____7160
                                                                    ::
                                                                    uu____7180
                                                                     in
                                                                    uu____7126
                                                                    ::
                                                                    uu____7146
                                                                     in
                                                                    uu____7092
                                                                    ::
                                                                    uu____7112
                                                                     in
                                                                    uu____7058
                                                                    ::
                                                                    uu____7078
                                                                     in
                                                                    uu____7024
                                                                    ::
                                                                    uu____7044
                                                                     in
                                                                    uu____6990
                                                                    ::
                                                                    uu____7010
                                                                     in
                                                                    uu____6956
                                                                    ::
                                                                    uu____6976
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____6942
                                                                     in
                                                                    uu____6908
                                                                    ::
                                                                    uu____6928
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____6894
                                                                     in
                                                                    uu____6860
                                                                    ::
                                                                    uu____6880
                                                                     in
                                                                    uu____6826
                                                                    ::
                                                                    uu____6846
                                                                     in
                                                                    uu____6792
                                                                    ::
                                                                    uu____6812
                                                                     in
                                                                    uu____6758
                                                                    ::
                                                                    uu____6778
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.valid_elim",
                                                                    BoolStr,
                                                                    "Include an axiom in the SMT encoding to eliminate proof-irrelevance into the existence of a proof witness")
                                                                    ::
                                                                    uu____6744
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.valid_intro",
                                                                    BoolStr,
                                                                    "Include an axiom in the SMT encoding to introduce proof-irrelevance from a constructive proof")
                                                                    ::
                                                                    uu____6730
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6716
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6702
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____6688
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____6674
                                                                     in
                                                                    uu____6640
                                                                    ::
                                                                    uu____6660
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____6626
                                                                     in
                                                                    uu____6592
                                                                    ::
                                                                    uu____6612
                                                                     in
                                                                    uu____6558
                                                                    ::
                                                                    uu____6578
                                                                     in
                                                                    uu____6524
                                                                    ::
                                                                    uu____6544
                                                                     in
                                                                    uu____6490
                                                                    ::
                                                                    uu____6510
                                                                     in
                                                                    uu____6456
                                                                    ::
                                                                    uu____6476
                                                                     in
                                                                    uu____6422
                                                                    ::
                                                                    uu____6442
                                                                     in
                                                                    uu____6388
                                                                    ::
                                                                    uu____6408
                                                                     in
                                                                    uu____6354
                                                                    ::
                                                                    uu____6374
                                                                     in
                                                                    uu____6320
                                                                    ::
                                                                    uu____6340
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____6306
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____6292
                                                                     in
                                                                    uu____6258
                                                                    ::
                                                                    uu____6278
                                                                     in
                                                                    uu____6224
                                                                    ::
                                                                    uu____6244
                                                                     in
                                                                    uu____6190
                                                                    ::
                                                                    uu____6210
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____6176
                                                                     in
                                                                    uu____6142
                                                                    ::
                                                                    uu____6162
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____6128
                                                                     in
                                                                    uu____6094
                                                                    ::
                                                                    uu____6114
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____6080
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____6066
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____6052
                                                                     in
                                                                    uu____6018
                                                                    ::
                                                                    uu____6038
                                                                     in
                                                                    uu____5984
                                                                    ::
                                                                    uu____6004
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____5970
                                                                     in
                                                                    uu____5936
                                                                    ::
                                                                    uu____5956
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    "Retain comments in the logged SMT queries (requires --log_queries; default true)")
                                                                    ::
                                                                    uu____5922
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____5908
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try initially (default 2)")
                                                                    ::
                                                                    uu____5894
                                                                     in
                                                                    uu____5860
                                                                    ::
                                                                    uu____5880
                                                                     in
                                                                  uu____5826
                                                                    ::
                                                                    uu____5846
                                                                   in
                                                                uu____5792 ::
                                                                  uu____5812
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "include",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "path")),
                                                                "A directory in which to search for files included on the command line")
                                                                :: uu____5778
                                                               in
                                                            uu____5744 ::
                                                              uu____5764
                                                             in
                                                          uu____5710 ::
                                                            uu____5730
                                                           in
                                                        uu____5676 ::
                                                          uu____5696
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "hint_file",
                                                        (PathStr "path"),
                                                        "Read/write hints to <path> (instead of module-specific hints files)")
                                                        :: uu____5662
                                                       in
                                                    uu____5628 :: uu____5648
                                                     in
                                                  uu____5594 :: uu____5614
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "extract_namespace",
                                                  (Accumulated
                                                     (PostProcessed
                                                        (pp_lowercase,
                                                          (SimpleStr
                                                             "namespace name")))),
                                                  "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                  :: uu____5580
                                                 in
                                              (FStar_Getopt.noshort,
                                                "extract_module",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "module_name")))),
                                                "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                                :: uu____5566
                                               in
                                            (FStar_Getopt.noshort, "extract",
                                              (Accumulated
                                                 (SimpleStr
                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                              "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                              :: uu____5552
                                             in
                                          uu____5518 :: uu____5538  in
                                        uu____5484 :: uu____5504  in
                                      (FStar_Getopt.noshort, "dump_module",
                                        (Accumulated
                                           (SimpleStr "module_name")), "")
                                        :: uu____5470
                                       in
                                    uu____5436 :: uu____5456  in
                                  uu____5402 :: uu____5422  in
                                uu____5368 :: uu____5388  in
                              (FStar_Getopt.noshort, "dep",
                                (EnumStr ["make"; "graph"; "full"; "raw"]),
                                "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                                :: uu____5354
                               in
                            (FStar_Getopt.noshort, "defensive",
                              (EnumStr ["no"; "warn"; "fail"]),
                              "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                              :: uu____5340
                             in
                          (FStar_Getopt.noshort, "debug_level",
                            (Accumulated
                               (OpenEnumStr
                                  (["Low"; "Medium"; "High"; "Extreme"],
                                    "..."))),
                            "Control the verbosity of debugging info") ::
                            uu____5326
                           in
                        (FStar_Getopt.noshort, "debug",
                          (Accumulated (SimpleStr "module_name")),
                          "Print lots of debugging information while checking module")
                          :: uu____5312
                         in
                      (FStar_Getopt.noshort, "codegen-lib",
                        (Accumulated (SimpleStr "namespace")),
                        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                        :: uu____5298
                       in
                    (FStar_Getopt.noshort, "codegen",
                      (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                      "Generate code for further compilation to executable code, or build a compiler plugin")
                      :: uu____5284
                     in
                  uu____5250 :: uu____5270  in
                uu____5216 :: uu____5236  in
              (FStar_Getopt.noshort, "cache_dir",
                (PostProcessed (pp_validate_dir, (PathStr "dir"))),
                "Read and write .checked and .checked.lax in directory <dir>")
                :: uu____5202
               in
            uu____5168 :: uu____5188  in
          (FStar_Getopt.noshort, "already_cached",
            (Accumulated
               (SimpleStr
                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
            "\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")
            :: uu____5154
           in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____5140
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____5126
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___7_9421  ->
             match uu___7_9421 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____5112

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____9450  ->
    let uu____9453 = specs_with_types ()  in
    FStar_List.map
      (fun uu____9484  ->
         match uu____9484 with
         | (short,long,typ,doc) ->
             let uu____9506 =
               let uu____9520 = arg_spec_of_opt_type long typ  in
               (short, long, uu____9520, doc)  in
             mk_spec uu____9506) uu____9453

let (settable : Prims.string -> Prims.bool) =
  fun uu___8_9535  ->
    match uu___8_9535 with
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
    | uu____9658 -> false
  
let (resettable : Prims.string -> Prims.bool) =
  fun s  ->
    (((((settable s) || (s = "z3seed")) || (s = "z3cliopt")) ||
        (s = "using_facts_from"))
       || (s = "smtencoding.valid_intro"))
      || (s = "smtencoding.valid_elim")
  
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
       (fun uu____9761  ->
          match uu____9761 with
          | (uu____9776,x,uu____9778,uu____9779) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____9854  ->
          match uu____9854 with
          | (uu____9869,x,uu____9871,uu____9872) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____9888  ->
    let uu____9889 = specs ()  in display_usage_aux uu____9889
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____9921 -> true
    | uu____9924 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____9934 -> uu____9934
  
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
        (fun uu___472_9955  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____9972 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____9972
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____9997  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____10003 =
             let uu____10007 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____10007 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____10003)
       in
    let uu____10064 =
      let uu____10068 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____10068
       in
    (res, uu____10064)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____10110  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____10153 = specs ()  in
       FStar_Getopt.parse_cmdline uu____10153 (fun x  -> ())  in
     (let uu____10160 =
        let uu____10166 =
          let uu____10167 = FStar_List.map mk_string old_verify_module  in
          List uu____10167  in
        ("verify_module", uu____10166)  in
      set_option' uu____10160);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____10186 =
        let uu____10188 =
          let uu____10190 =
            let uu____10192 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____10192  in
          (FStar_String.length f1) - uu____10190  in
        uu____10188 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____10186  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____10205 = get_lax ()  in
    if uu____10205
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____10226 = module_name_of_file_name fn  in
    should_verify uu____10226
  
let (module_name_eq : Prims.string -> Prims.string -> Prims.bool) =
  fun m1  ->
    fun m2  -> (FStar_String.lowercase m1) = (FStar_String.lowercase m2)
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____10254 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____10254 (FStar_List.existsb (module_name_eq m))
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____10272 = should_verify m  in
    if uu____10272 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____10289  ->
    let cache_dir =
      let uu____10294 = get_cache_dir ()  in
      match uu____10294 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some c -> [c]  in
    let uu____10308 = get_no_default_includes ()  in
    if uu____10308
    then
      let uu____10314 = get_include ()  in
      FStar_List.append cache_dir uu____10314
    else
      (let lib_paths =
         let uu____10325 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____10325 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = FStar_String.op_Hat fstar_bin_directory "/.."
                in
             let defs = universe_include_path_base_dirs  in
             let uu____10341 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> FStar_String.op_Hat fstar_home x))
                in
             FStar_All.pipe_right uu____10341
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____10368 =
         let uu____10372 =
           let uu____10376 = get_include ()  in
           FStar_List.append uu____10376 ["."]  in
         FStar_List.append lib_paths uu____10372  in
       FStar_List.append cache_dir uu____10368)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____10407 = FStar_Util.smap_try_find file_map filename  in
    match uu____10407 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___523_10438  ->
               match () with
               | () ->
                   let uu____10442 = FStar_Util.is_path_absolute filename  in
                   if uu____10442
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____10458 =
                        let uu____10462 = include_path ()  in
                        FStar_List.rev uu____10462  in
                      FStar_Util.find_map uu____10458
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___522_10490 -> FStar_Pervasives_Native.None  in
        (if FStar_Option.isSome result
         then FStar_Util.smap_add file_map filename result
         else ();
         result)
  
let (prims : unit -> Prims.string) =
  fun uu____10509  ->
    let uu____10510 = get_prims ()  in
    match uu____10510 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____10519 = find_file filename  in
        (match uu____10519 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____10528 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____10528)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____10541  ->
    let uu____10542 = prims ()  in FStar_Util.basename uu____10542
  
let (pervasives : unit -> Prims.string) =
  fun uu____10550  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____10554 = find_file filename  in
    match uu____10554 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____10563 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____10563
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____10573  ->
    let uu____10574 = pervasives ()  in FStar_Util.basename uu____10574
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____10582  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____10586 = find_file filename  in
    match uu____10586 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____10595 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____10595
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____10608 = get_odir ()  in
    match uu____10608 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____10626 = get_cache_dir ()  in
    match uu____10626 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____10635 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____10635
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns  ->
    let cache = FStar_Util.smap_create (Prims.parse_int "31")  in
    let with_cache f s =
      let uu____10757 = FStar_Util.smap_try_find cache s  in
      match uu____10757 with
      | FStar_Pervasives_Native.Some s1 -> s1
      | FStar_Pervasives_Native.None  ->
          let res = f s  in (FStar_Util.smap_add cache s res; res)
       in
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if s = "-*"
        then ([], false)
        else
          if FStar_Util.starts_with s "-"
          then
            (let path =
               let uu____10911 =
                 FStar_Util.substring_from s (Prims.parse_int "1")  in
               path_of_text uu____10911  in
             (path, false))
          else
            (let s1 =
               if FStar_Util.starts_with s "+"
               then FStar_Util.substring_from s (Prims.parse_int "1")
               else s  in
             ((path_of_text s1), true))
       in
    let uu____10934 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              let s1 = FStar_Util.trim_string s  in
              if s1 = ""
              then []
              else
                with_cache
                  (fun s2  ->
                     let uu____11002 =
                       let uu____11006 =
                         FStar_All.pipe_right (FStar_Util.splitlines s2)
                           (FStar_List.concatMap
                              (fun s3  -> FStar_Util.split s3 " "))
                          in
                       FStar_All.pipe_right uu____11006
                         (FStar_List.filter (fun s3  -> s3 <> ""))
                        in
                     FStar_All.pipe_right uu____11002
                       (FStar_List.map parse_one_setting)) s1))
       in
    FStar_All.pipe_right uu____10934 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____11093 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____11093 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____11108  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____11117  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11126  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____11133  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____11140  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____11147  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____11157 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____11168 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____11179 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____11190 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____11199  ->
    let uu____11200 = get_codegen ()  in
    FStar_Util.map_opt uu____11200
      (fun uu___9_11206  ->
         match uu___9_11206 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____11212 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____11225  ->
    let uu____11226 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____11226
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____11252  -> let uu____11253 = get_debug ()  in uu____11253 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____11270 = get_debug ()  in
    FStar_All.pipe_right uu____11270
      (FStar_List.existsb (module_name_eq modul))
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____11295 = get_debug ()  in
       FStar_All.pipe_right uu____11295
         (FStar_List.existsb (module_name_eq modul)))
        && (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____11310  ->
    let uu____11311 = get_defensive ()  in uu____11311 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____11321  ->
    let uu____11322 = get_defensive ()  in uu____11322 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11334  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____11341  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____11348  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____11355  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____11365 = get_dump_module ()  in
    FStar_All.pipe_right uu____11365 (FStar_List.existsb (module_name_eq s))
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____11380  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____11387  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____11397 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____11397
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____11433  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____11441  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____11448  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11457  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____11464  -> get_ide () 
let (print : unit -> Prims.bool) = fun uu____11471  -> get_print () 
let (print_in_place : unit -> Prims.bool) =
  fun uu____11478  -> get_print_in_place () 
let profile : 'a . (unit -> 'a) -> ('a -> Prims.string) -> 'a =
  fun f  ->
    fun msg  ->
      let uu____11509 = get_profile ()  in
      if uu____11509
      then
        let uu____11512 = FStar_Util.record_time f  in
        match uu____11512 with
        | (a,time) ->
            ((let uu____11523 = FStar_Util.string_of_int time  in
              let uu____11525 = msg a  in
              FStar_Util.print2 "Elapsed time %s ms: %s\n" uu____11523
                uu____11525);
             a)
      else f ()
  
let (initial_fuel : unit -> Prims.int) =
  fun uu____11536  ->
    let uu____11537 = get_initial_fuel ()  in
    let uu____11539 = get_max_fuel ()  in Prims.min uu____11537 uu____11539
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____11547  ->
    let uu____11548 = get_initial_ifuel ()  in
    let uu____11550 = get_max_ifuel ()  in Prims.min uu____11548 uu____11550
  
let (interactive : unit -> Prims.bool) =
  fun uu____11558  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____11565  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____11574  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____11581  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____11588  -> get_log_queries () 
let (keep_query_captions : unit -> Prims.bool) =
  fun uu____11595  -> (log_queries ()) && (get_keep_query_captions ()) 
let (log_types : unit -> Prims.bool) = fun uu____11602  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____11609  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____11616  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____11623  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____11630  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____11636  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____11645  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____11652  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____11662 = get_no_extract ()  in
    FStar_All.pipe_right uu____11662 (FStar_List.existsb (module_name_eq s))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____11677  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____11684  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____11691  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____11698  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11707  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____11714  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____11721  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____11728  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____11735  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____11742  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____11749  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____11756  -> get_print_z3_statistics () 
let (query_stats : unit -> Prims.bool) =
  fun uu____11763  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____11770  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11779  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____11786  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____11793  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____11800  ->
    let uu____11801 = get_smtencoding_nl_arith_repr ()  in
    uu____11801 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____11811  ->
    let uu____11812 = get_smtencoding_nl_arith_repr ()  in
    uu____11812 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____11822  ->
    let uu____11823 = get_smtencoding_nl_arith_repr ()  in
    uu____11823 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____11833  ->
    let uu____11834 = get_smtencoding_l_arith_repr ()  in
    uu____11834 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____11844  ->
    let uu____11845 = get_smtencoding_l_arith_repr ()  in
    uu____11845 = "boxwrap"
  
let (smtencoding_valid_intro : unit -> Prims.bool) =
  fun uu____11855  -> get_smtencoding_valid_intro () 
let (smtencoding_valid_elim : unit -> Prims.bool) =
  fun uu____11862  -> get_smtencoding_valid_elim () 
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____11869  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____11876  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____11883  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____11890  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____11897  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____11904  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____11911  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____11918  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____11925  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____11932  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____11939  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____11946  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____11953  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____11960  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11969  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____11976  -> get_use_tactics () 
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu____11992  ->
    let uu____11993 = get_using_facts_from ()  in
    match uu____11993 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____12047  ->
    let uu____12048 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____12048
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____12059  ->
    let uu____12060 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____12060 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____12068 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____12079  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____12086  ->
    let uu____12087 = get_smt ()  in
    match uu____12087 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____12105  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____12112  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____12119  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____12126  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____12133  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____12140  ->
    (get_use_two_phase_tc ()) &&
      (let uu____12142 = lax ()  in Prims.op_Negation uu____12142)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____12150  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____12157  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____12164  ->
    let uu____12165 = get_warn_error ()  in
    FStar_String.concat "" uu____12165
  
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____12176  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____12183  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____12200 =
      let uu____12202 = trace_error ()  in Prims.op_Negation uu____12202  in
    if uu____12200
    then
      (push ();
       (let r =
          try
            (fun uu___723_12217  ->
               match () with
               | () -> let uu____12222 = f ()  in FStar_Util.Inr uu____12222)
              ()
          with | uu___722_12224 -> FStar_Util.Inl uu___722_12224  in
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
        | (uu____12305,[]) -> true
        | (m2::ms,p::ps) ->
            (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
        | uu____12338 -> false  in
      let uu____12350 =
        FStar_All.pipe_right setting
          (FStar_Util.try_find
             (fun uu____12392  ->
                match uu____12392 with
                | (path,uu____12403) -> matches_path m_components path))
         in
      match uu____12350 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____12422,flag) -> flag
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____12451 = get_extract ()  in
    match uu____12451 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____12466 =
            let uu____12482 = get_no_extract ()  in
            let uu____12486 = get_extract_namespace ()  in
            let uu____12490 = get_extract_module ()  in
            (uu____12482, uu____12486, uu____12490)  in
          match uu____12466 with
          | ([],[],[]) -> ()
          | uu____12515 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         module_matches_namespace_filter m1 extract_setting)
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____12544 = get_extract_namespace ()  in
          match uu____12544 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____12572 = get_extract_module ()  in
          match uu____12572 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____12594 = no_extract m1  in Prims.op_Negation uu____12594)
          &&
          (let uu____12597 =
             let uu____12608 = get_extract_namespace ()  in
             let uu____12612 = get_extract_module ()  in
             (uu____12608, uu____12612)  in
           (match uu____12597 with
            | ([],[]) -> true
            | uu____12632 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  
let (should_be_already_cached : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____12652 = get_already_cached ()  in
    match uu____12652 with
    | FStar_Pervasives_Native.None  -> false
    | FStar_Pervasives_Native.Some already_cached_setting ->
        module_matches_namespace_filter m already_cached_setting
  
let (error_flags : unit -> error_flag Prims.list) =
  let cache = FStar_Util.smap_create (Prims.parse_int "10")  in
  fun uu____12685  ->
    let we = warn_error ()  in
    let uu____12688 = FStar_Util.smap_try_find cache we  in
    match uu____12688 with
    | FStar_Pervasives_Native.None  ->
        let r = parse_warn_error we  in (FStar_Util.smap_add cache we r; r)
    | FStar_Pervasives_Native.Some r -> r
  