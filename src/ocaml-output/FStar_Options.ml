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
  ("protect_top_level_axioms", (Bool true));
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
let (parse_warn_error_set_get :
  (((Prims.string -> error_flag Prims.list) -> unit) *
    (unit -> Prims.string -> error_flag Prims.list)))
  =
  let r = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let set1 f =
    let uu____2294 = FStar_ST.op_Bang r  in
    match uu____2294 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some f)
    | uu____2385 -> failwith "Multiple initialization of FStar.Options"  in
  let get1 uu____2406 =
    let uu____2407 = FStar_ST.op_Bang r  in
    match uu____2407 with
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
    let uu____2546 = FStar_Pervasives_Native.snd parse_warn_error_set_get ()
       in
    uu____2546 s
  
let (init : unit -> unit) =
  fun uu____2577  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____2597  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____2670 =
      let uu____2673 = peek ()  in FStar_Util.smap_try_find uu____2673 s  in
    match uu____2670 with
    | FStar_Pervasives_Native.None  ->
        let uu____2676 =
          let uu____2678 = FStar_String.op_Hat s " not found"  in
          FStar_String.op_Hat "Impossible: option " uu____2678  in
        failwith uu____2676
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____2690 . Prims.string -> (option_val -> 'Auu____2690) -> 'Auu____2690
  = fun s  -> fun c  -> let uu____2708 = get_option s  in c uu____2708 
let (get_abort_on : unit -> Prims.int) =
  fun uu____2715  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____2724  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____2735  -> lookup_opt "admit_except" (as_option as_string) 
let (get_already_cached :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2751  ->
    lookup_opt "already_cached" (as_option (as_list as_string))
  
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____2768  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2779  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____2791  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____2800  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2811  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____2825  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____2839  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____2853  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____2864  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2875  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____2887  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____2896  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____2905  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____2916  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____2928  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____2937  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2950  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____2969  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____2983  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____2995  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____3004  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____3013  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3024  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____3036  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____3045  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____3056  -> lookup_opt "include" (as_list as_string) 
let (get_print : unit -> Prims.bool) =
  fun uu____3068  -> lookup_opt "print" as_bool 
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____3077  -> lookup_opt "print_in_place" as_bool 
let (get_profile : unit -> Prims.bool) =
  fun uu____3086  -> lookup_opt "profile" as_bool 
let (get_protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____3095  -> lookup_opt "protect_top_level_axioms" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____3104  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____3113  -> lookup_opt "initial_ifuel" as_int 
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu____3122  -> lookup_opt "keep_query_captions" as_bool 
let (get_lax : unit -> Prims.bool) =
  fun uu____3131  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____3142  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____3154  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____3163  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____3172  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____3181  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____3190  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____3199  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____3208  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____3217  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____3228  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____3240  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____3249  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____3258  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____3267  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3278  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____3290  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3301  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____3313  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____3322  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____3331  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____3340  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____3349  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____3358  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____3367  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____3376  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____3385  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3396  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____3408  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3419  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____3431  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____3440  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____3449  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____3458  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____3467  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____3476  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____3485  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____3494  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____3503  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____3512  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____3521  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____3530  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____3539  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____3548  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____3557  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____3566  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____3575  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3586  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____3598  ->
    let uu____3599 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____3599
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____3613  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3632  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____3646  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____3660  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____3672  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____3681  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____3692  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____3704  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____3713  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____3722  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____3731  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____3740  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____3749  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____3758  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____3767  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____3776  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____3785  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___6_3794  ->
    match uu___6_3794 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____3815 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____3824 = get_debug_level ()  in
    FStar_All.pipe_right uu____3824
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "<not set>" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____3880  ->
    let uu____3881 =
      let uu____3883 = FStar_ST.op_Bang _version  in
      let uu____3906 = FStar_ST.op_Bang _platform  in
      let uu____3929 = FStar_ST.op_Bang _compiler  in
      let uu____3952 = FStar_ST.op_Bang _date  in
      let uu____3975 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____3883
        uu____3906 uu____3929 uu____3952 uu____3975
       in
    FStar_Util.print_string uu____3881
  
let display_usage_aux :
  'Auu____4006 'Auu____4007 .
    ('Auu____4006 * Prims.string * 'Auu____4007 FStar_Getopt.opt_variant *
      Prims.string) Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____4062  ->
         match uu____4062 with
         | (uu____4075,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____4094 =
                      let uu____4096 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____4096  in
                    FStar_Util.print_string uu____4094
                  else
                    (let uu____4101 =
                       let uu____4103 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____4103 doc  in
                     FStar_Util.print_string uu____4101)
              | FStar_Getopt.OneArg (uu____4106,argname) ->
                  if doc = ""
                  then
                    let uu____4121 =
                      let uu____4123 = FStar_Util.colorize_bold flag  in
                      let uu____4125 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____4123 uu____4125
                       in
                    FStar_Util.print_string uu____4121
                  else
                    (let uu____4130 =
                       let uu____4132 = FStar_Util.colorize_bold flag  in
                       let uu____4134 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____4132
                         uu____4134 doc
                        in
                     FStar_Util.print_string uu____4130))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____4169 = o  in
    match uu____4169 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____4211 =
                let uu____4212 = f ()  in set_option name uu____4212  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____4233 = f x  in set_option name uu____4233
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____4260 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____4260  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____4286 =
        let uu____4289 = lookup_opt name as_list'  in
        FStar_List.append uu____4289 [value]  in
      mk_list uu____4286
  
let accumulate_string :
  'Auu____4303 .
    Prims.string -> ('Auu____4303 -> Prims.string) -> 'Auu____4303 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____4328 =
          let uu____4329 =
            let uu____4330 = post_processor value  in mk_string uu____4330
             in
          accumulated_option name uu____4329  in
        set_option name uu____4328
  
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
    match projectee with | Const _0 -> true | uu____4452 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____4472 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____4493 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____4506 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____4529 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____4554 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____4590 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____4640 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____4680 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____4699 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____4725 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____4768 -> true
    | uu____4771 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____4781 -> uu____4781
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___292_4805  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____4807 ->
                      let uu____4809 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____4809 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____4817 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____4817
                  | PathStr uu____4834 -> mk_path str_val
                  | SimpleStr uu____4836 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____4846 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____4863 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____4863
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
            let uu____4883 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____4883
  
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ  ->
    let desc_of_enum cases =
      let uu____4913 =
        let uu____4915 =
          FStar_String.op_Hat (FStar_String.concat "|" cases) "]"  in
        FStar_String.op_Hat "[" uu____4915  in
      FStar_Pervasives_Native.Some uu____4913  in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____4957,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____4967,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____4998 = desc_of_opt_type typ  in
      match uu____4998 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____5006  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____5032 =
      let uu____5034 = as_string s  in FStar_String.lowercase uu____5034  in
    mk_string uu____5032
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string)
      Prims.list)
  =
  fun uu____5069  ->
    let uu____5083 =
      let uu____5097 =
        let uu____5111 =
          let uu____5125 =
            let uu____5139 =
              let uu____5151 =
                let uu____5152 = mk_bool true  in Const uu____5152  in
              (FStar_Getopt.noshort, "cache_checked_modules", uu____5151,
                "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
               in
            let uu____5159 =
              let uu____5173 =
                let uu____5187 =
                  let uu____5199 =
                    let uu____5200 = mk_bool true  in Const uu____5200  in
                  (FStar_Getopt.noshort, "cache_off", uu____5199,
                    "Do not read or write any .checked files")
                   in
                let uu____5207 =
                  let uu____5221 =
                    let uu____5233 =
                      let uu____5234 = mk_bool true  in Const uu____5234  in
                    (FStar_Getopt.noshort, "cmi", uu____5233,
                      "Inline across module interfaces during extraction (aka. cross-module inlining)")
                     in
                  let uu____5241 =
                    let uu____5255 =
                      let uu____5269 =
                        let uu____5283 =
                          let uu____5297 =
                            let uu____5311 =
                              let uu____5325 =
                                let uu____5339 =
                                  let uu____5351 =
                                    let uu____5352 = mk_bool true  in
                                    Const uu____5352  in
                                  (FStar_Getopt.noshort, "detail_errors",
                                    uu____5351,
                                    "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                   in
                                let uu____5359 =
                                  let uu____5373 =
                                    let uu____5385 =
                                      let uu____5386 = mk_bool true  in
                                      Const uu____5386  in
                                    (FStar_Getopt.noshort,
                                      "detail_hint_replay", uu____5385,
                                      "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                     in
                                  let uu____5393 =
                                    let uu____5407 =
                                      let uu____5419 =
                                        let uu____5420 = mk_bool true  in
                                        Const uu____5420  in
                                      (FStar_Getopt.noshort, "doc",
                                        uu____5419,
                                        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                       in
                                    let uu____5427 =
                                      let uu____5441 =
                                        let uu____5455 =
                                          let uu____5467 =
                                            let uu____5468 = mk_bool true  in
                                            Const uu____5468  in
                                          (FStar_Getopt.noshort,
                                            "eager_inference", uu____5467,
                                            "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                           in
                                        let uu____5475 =
                                          let uu____5489 =
                                            let uu____5501 =
                                              let uu____5502 = mk_bool true
                                                 in
                                              Const uu____5502  in
                                            (FStar_Getopt.noshort,
                                              "eager_subtyping", uu____5501,
                                              "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                             in
                                          let uu____5509 =
                                            let uu____5523 =
                                              let uu____5537 =
                                                let uu____5551 =
                                                  let uu____5565 =
                                                    let uu____5577 =
                                                      let uu____5578 =
                                                        mk_bool true  in
                                                      Const uu____5578  in
                                                    (FStar_Getopt.noshort,
                                                      "expose_interfaces",
                                                      uu____5577,
                                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                     in
                                                  let uu____5585 =
                                                    let uu____5599 =
                                                      let uu____5611 =
                                                        let uu____5612 =
                                                          mk_bool true  in
                                                        Const uu____5612  in
                                                      (FStar_Getopt.noshort,
                                                        "hide_uvar_nums",
                                                        uu____5611,
                                                        "Don't print unification variable numbers")
                                                       in
                                                    let uu____5619 =
                                                      let uu____5633 =
                                                        let uu____5647 =
                                                          let uu____5659 =
                                                            let uu____5660 =
                                                              mk_bool true
                                                               in
                                                            Const uu____5660
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "hint_info",
                                                            uu____5659,
                                                            "Print information regarding hints (deprecated; use --query_stats instead)")
                                                           in
                                                        let uu____5667 =
                                                          let uu____5681 =
                                                            let uu____5693 =
                                                              let uu____5694
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____5694
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "in",
                                                              uu____5693,
                                                              "Legacy interactive mode; reads input from stdin")
                                                             in
                                                          let uu____5701 =
                                                            let uu____5715 =
                                                              let uu____5727
                                                                =
                                                                let uu____5728
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____5728
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "ide",
                                                                uu____5727,
                                                                "JSON-based interactive mode for IDEs")
                                                               in
                                                            let uu____5735 =
                                                              let uu____5749
                                                                =
                                                                let uu____5763
                                                                  =
                                                                  let uu____5775
                                                                    =
                                                                    let uu____5776
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5776
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "print",
                                                                    uu____5775,
                                                                    "Parses and prettyprints the files included on the command line")
                                                                   in
                                                                let uu____5783
                                                                  =
                                                                  let uu____5797
                                                                    =
                                                                    let uu____5809
                                                                    =
                                                                    let uu____5810
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5810
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_in_place",
                                                                    uu____5809,
                                                                    "Parses and prettyprints in place the files included on the command line")
                                                                     in
                                                                  let uu____5817
                                                                    =
                                                                    let uu____5831
                                                                    =
                                                                    let uu____5843
                                                                    =
                                                                    let uu____5844
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5844
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "profile",
                                                                    uu____5843,
                                                                    "Prints timing information for various operations in the compiler")
                                                                     in
                                                                    let uu____5851
                                                                    =
                                                                    let uu____5865
                                                                    =
                                                                    let uu____5879
                                                                    =
                                                                    let uu____5893
                                                                    =
                                                                    let uu____5907
                                                                    =
                                                                    let uu____5921
                                                                    =
                                                                    let uu____5933
                                                                    =
                                                                    let uu____5934
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5934
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____5933,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____5941
                                                                    =
                                                                    let uu____5955
                                                                    =
                                                                    let uu____5969
                                                                    =
                                                                    let uu____5981
                                                                    =
                                                                    let uu____5982
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5982
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____5981,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____5989
                                                                    =
                                                                    let uu____6003
                                                                    =
                                                                    let uu____6015
                                                                    =
                                                                    let uu____6016
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6016
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____6015,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____6023
                                                                    =
                                                                    let uu____6037
                                                                    =
                                                                    let uu____6051
                                                                    =
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
                                                                    "MLish",
                                                                    uu____6091,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____6099
                                                                    =
                                                                    let uu____6113
                                                                    =
                                                                    let uu____6127
                                                                    =
                                                                    let uu____6139
                                                                    =
                                                                    let uu____6140
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6140
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____6139,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____6147
                                                                    =
                                                                    let uu____6161
                                                                    =
                                                                    let uu____6175
                                                                    =
                                                                    let uu____6187
                                                                    =
                                                                    let uu____6188
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6188
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____6187,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____6195
                                                                    =
                                                                    let uu____6209
                                                                    =
                                                                    let uu____6221
                                                                    =
                                                                    let uu____6222
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6222
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____6221,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____6229
                                                                    =
                                                                    let uu____6243
                                                                    =
                                                                    let uu____6255
                                                                    =
                                                                    let uu____6256
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6256
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____6255,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____6263
                                                                    =
                                                                    let uu____6277
                                                                    =
                                                                    let uu____6291
                                                                    =
                                                                    let uu____6305
                                                                    =
                                                                    let uu____6317
                                                                    =
                                                                    let uu____6318
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6318
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____6317,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____6325
                                                                    =
                                                                    let uu____6339
                                                                    =
                                                                    let uu____6351
                                                                    =
                                                                    let uu____6352
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6352
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____6351,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____6359
                                                                    =
                                                                    let uu____6373
                                                                    =
                                                                    let uu____6385
                                                                    =
                                                                    let uu____6386
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6386
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____6385,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____6393
                                                                    =
                                                                    let uu____6407
                                                                    =
                                                                    let uu____6419
                                                                    =
                                                                    let uu____6420
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6420
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____6419,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____6427
                                                                    =
                                                                    let uu____6441
                                                                    =
                                                                    let uu____6453
                                                                    =
                                                                    let uu____6454
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6454
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____6453,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____6461
                                                                    =
                                                                    let uu____6475
                                                                    =
                                                                    let uu____6487
                                                                    =
                                                                    let uu____6488
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6488
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____6487,
                                                                    "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)")
                                                                     in
                                                                    let uu____6495
                                                                    =
                                                                    let uu____6509
                                                                    =
                                                                    let uu____6521
                                                                    =
                                                                    let uu____6522
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6522
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____6521,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____6529
                                                                    =
                                                                    let uu____6543
                                                                    =
                                                                    let uu____6555
                                                                    =
                                                                    let uu____6556
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6556
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____6555,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____6563
                                                                    =
                                                                    let uu____6577
                                                                    =
                                                                    let uu____6589
                                                                    =
                                                                    let uu____6590
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6590
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____6589,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____6597
                                                                    =
                                                                    let uu____6611
                                                                    =
                                                                    let uu____6625
                                                                    =
                                                                    let uu____6637
                                                                    =
                                                                    let uu____6638
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6638
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____6637,
                                                                    "Disable all non-critical output")
                                                                     in
                                                                    let uu____6645
                                                                    =
                                                                    let uu____6659
                                                                    =
                                                                    let uu____6673
                                                                    =
                                                                    let uu____6687
                                                                    =
                                                                    let uu____6701
                                                                    =
                                                                    let uu____6715
                                                                    =
                                                                    let uu____6727
                                                                    =
                                                                    let uu____6728
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6728
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____6727,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____6735
                                                                    =
                                                                    let uu____6749
                                                                    =
                                                                    let uu____6761
                                                                    =
                                                                    let uu____6762
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6762
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____6761,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____6769
                                                                    =
                                                                    let uu____6783
                                                                    =
                                                                    let uu____6795
                                                                    =
                                                                    let uu____6796
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6796
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____6795,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____6803
                                                                    =
                                                                    let uu____6817
                                                                    =
                                                                    let uu____6829
                                                                    =
                                                                    let uu____6830
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6830
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____6829,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____6837
                                                                    =
                                                                    let uu____6851
                                                                    =
                                                                    let uu____6865
                                                                    =
                                                                    let uu____6877
                                                                    =
                                                                    let uu____6878
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6878
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____6877,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____6885
                                                                    =
                                                                    let uu____6899
                                                                    =
                                                                    let uu____6913
                                                                    =
                                                                    let uu____6925
                                                                    =
                                                                    let uu____6926
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6926
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____6925,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
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
                                                                    "trace_error",
                                                                    uu____6959,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____6967
                                                                    =
                                                                    let uu____6981
                                                                    =
                                                                    let uu____6993
                                                                    =
                                                                    let uu____6994
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6994
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____6993,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____7001
                                                                    =
                                                                    let uu____7015
                                                                    =
                                                                    let uu____7027
                                                                    =
                                                                    let uu____7028
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7028
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____7027,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____7035
                                                                    =
                                                                    let uu____7049
                                                                    =
                                                                    let uu____7061
                                                                    =
                                                                    let uu____7062
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7062
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____7061,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____7069
                                                                    =
                                                                    let uu____7083
                                                                    =
                                                                    let uu____7095
                                                                    =
                                                                    let uu____7096
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7096
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____7095,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____7103
                                                                    =
                                                                    let uu____7117
                                                                    =
                                                                    let uu____7129
                                                                    =
                                                                    let uu____7130
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7130
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____7129,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____7137
                                                                    =
                                                                    let uu____7151
                                                                    =
                                                                    let uu____7163
                                                                    =
                                                                    let uu____7164
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7164
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____7163,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____7171
                                                                    =
                                                                    let uu____7185
                                                                    =
                                                                    let uu____7199
                                                                    =
                                                                    let uu____7211
                                                                    =
                                                                    let uu____7212
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7212
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____7211,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____7219
                                                                    =
                                                                    let uu____7233
                                                                    =
                                                                    let uu____7245
                                                                    =
                                                                    let uu____7246
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7246
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____7245,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____7253
                                                                    =
                                                                    let uu____7267
                                                                    =
                                                                    let uu____7281
                                                                    =
                                                                    let uu____7295
                                                                    =
                                                                    let uu____7309
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
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____7321,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____7329
                                                                    =
                                                                    let uu____7343
                                                                    =
                                                                    let uu____7355
                                                                    =
                                                                    let uu____7356
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
                                                                    ((fun
                                                                    uu____7372
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____7364)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7356
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____7355,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____7381
                                                                    =
                                                                    let uu____7395
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
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____7407,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____7415
                                                                    =
                                                                    let uu____7429
                                                                    =
                                                                    let uu____7443
                                                                    =
                                                                    let uu____7455
                                                                    =
                                                                    let uu____7456
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7456
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____7455,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____7463
                                                                    =
                                                                    let uu____7477
                                                                    =
                                                                    let uu____7491
                                                                    =
                                                                    let uu____7505
                                                                    =
                                                                    let uu____7519
                                                                    =
                                                                    let uu____7533
                                                                    =
                                                                    let uu____7545
                                                                    =
                                                                    let uu____7546
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7546
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____7545,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____7553
                                                                    =
                                                                    let uu____7567
                                                                    =
                                                                    let uu____7579
                                                                    =
                                                                    let uu____7580
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7580
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____7579,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____7587
                                                                    =
                                                                    let uu____7601
                                                                    =
                                                                    let uu____7615
                                                                    =
                                                                    let uu____7629
                                                                    =
                                                                    let uu____7643
                                                                    =
                                                                    let uu____7655
                                                                    =
                                                                    let uu____7656
                                                                    =
                                                                    let uu____7664
                                                                    =
                                                                    let uu____7665
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7665
                                                                     in
                                                                    ((fun
                                                                    uu____7671
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____7664)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7656
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____7655,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____7699
                                                                    =
                                                                    let uu____7713
                                                                    =
                                                                    let uu____7725
                                                                    =
                                                                    let uu____7726
                                                                    =
                                                                    let uu____7734
                                                                    =
                                                                    let uu____7735
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7735
                                                                     in
                                                                    ((fun
                                                                    uu____7741
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____7734)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7726
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____7725,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____7769
                                                                    =
                                                                    let uu____7783
                                                                    =
                                                                    let uu____7795
                                                                    =
                                                                    let uu____7796
                                                                    =
                                                                    let uu____7804
                                                                    =
                                                                    let uu____7805
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7805
                                                                     in
                                                                    ((fun
                                                                    uu____7812
                                                                     ->
                                                                    (
                                                                    let uu____7814
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____7814);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____7804)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7796
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____7795,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____7783]
                                                                     in
                                                                    uu____7713
                                                                    ::
                                                                    uu____7769
                                                                     in
                                                                    uu____7643
                                                                    ::
                                                                    uu____7699
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____7629
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____7615
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____7601
                                                                     in
                                                                    uu____7567
                                                                    ::
                                                                    uu____7587
                                                                     in
                                                                    uu____7533
                                                                    ::
                                                                    uu____7553
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____7519
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____7505
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____7491
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____7477
                                                                     in
                                                                    uu____7443
                                                                    ::
                                                                    uu____7463
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____7429
                                                                     in
                                                                    uu____7395
                                                                    ::
                                                                    uu____7415
                                                                     in
                                                                    uu____7343
                                                                    ::
                                                                    uu____7381
                                                                     in
                                                                    uu____7309
                                                                    ::
                                                                    uu____7329
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____7295
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____7281
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____7267
                                                                     in
                                                                    uu____7233
                                                                    ::
                                                                    uu____7253
                                                                     in
                                                                    uu____7199
                                                                    ::
                                                                    uu____7219
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____7185
                                                                     in
                                                                    uu____7151
                                                                    ::
                                                                    uu____7171
                                                                     in
                                                                    uu____7117
                                                                    ::
                                                                    uu____7137
                                                                     in
                                                                    uu____7083
                                                                    ::
                                                                    uu____7103
                                                                     in
                                                                    uu____7049
                                                                    ::
                                                                    uu____7069
                                                                     in
                                                                    uu____7015
                                                                    ::
                                                                    uu____7035
                                                                     in
                                                                    uu____6981
                                                                    ::
                                                                    uu____7001
                                                                     in
                                                                    uu____6947
                                                                    ::
                                                                    uu____6967
                                                                     in
                                                                    uu____6913
                                                                    ::
                                                                    uu____6933
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____6899
                                                                     in
                                                                    uu____6865
                                                                    ::
                                                                    uu____6885
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____6851
                                                                     in
                                                                    uu____6817
                                                                    ::
                                                                    uu____6837
                                                                     in
                                                                    uu____6783
                                                                    ::
                                                                    uu____6803
                                                                     in
                                                                    uu____6749
                                                                    ::
                                                                    uu____6769
                                                                     in
                                                                    uu____6715
                                                                    ::
                                                                    uu____6735
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6701
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6687
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____6673
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____6659
                                                                     in
                                                                    uu____6625
                                                                    ::
                                                                    uu____6645
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____6611
                                                                     in
                                                                    uu____6577
                                                                    ::
                                                                    uu____6597
                                                                     in
                                                                    uu____6543
                                                                    ::
                                                                    uu____6563
                                                                     in
                                                                    uu____6509
                                                                    ::
                                                                    uu____6529
                                                                     in
                                                                    uu____6475
                                                                    ::
                                                                    uu____6495
                                                                     in
                                                                    uu____6441
                                                                    ::
                                                                    uu____6461
                                                                     in
                                                                    uu____6407
                                                                    ::
                                                                    uu____6427
                                                                     in
                                                                    uu____6373
                                                                    ::
                                                                    uu____6393
                                                                     in
                                                                    uu____6339
                                                                    ::
                                                                    uu____6359
                                                                     in
                                                                    uu____6305
                                                                    ::
                                                                    uu____6325
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____6291
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____6277
                                                                     in
                                                                    uu____6243
                                                                    ::
                                                                    uu____6263
                                                                     in
                                                                    uu____6209
                                                                    ::
                                                                    uu____6229
                                                                     in
                                                                    uu____6175
                                                                    ::
                                                                    uu____6195
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____6161
                                                                     in
                                                                    uu____6127
                                                                    ::
                                                                    uu____6147
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____6113
                                                                     in
                                                                    uu____6079
                                                                    ::
                                                                    uu____6099
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____6065
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____6051
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____6037
                                                                     in
                                                                    uu____6003
                                                                    ::
                                                                    uu____6023
                                                                     in
                                                                    uu____5969
                                                                    ::
                                                                    uu____5989
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____5955
                                                                     in
                                                                    uu____5921
                                                                    ::
                                                                    uu____5941
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    "Retain comments in the logged SMT queries (requires --log_queries; default true)")
                                                                    ::
                                                                    uu____5907
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____5893
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try initially (default 2)")
                                                                    ::
                                                                    uu____5879
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "protect_top_level_axioms",
                                                                    BoolStr,
                                                                    "Guard nullary top-level symbols in the SMT encoding from provide ambient ground facts (default 'true')")
                                                                    ::
                                                                    uu____5865
                                                                     in
                                                                    uu____5831
                                                                    ::
                                                                    uu____5851
                                                                     in
                                                                  uu____5797
                                                                    ::
                                                                    uu____5817
                                                                   in
                                                                uu____5763 ::
                                                                  uu____5783
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "include",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "path")),
                                                                "A directory in which to search for files included on the command line")
                                                                :: uu____5749
                                                               in
                                                            uu____5715 ::
                                                              uu____5735
                                                             in
                                                          uu____5681 ::
                                                            uu____5701
                                                           in
                                                        uu____5647 ::
                                                          uu____5667
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "hint_file",
                                                        (PathStr "path"),
                                                        "Read/write hints to <path> (instead of module-specific hints files)")
                                                        :: uu____5633
                                                       in
                                                    uu____5599 :: uu____5619
                                                     in
                                                  uu____5565 :: uu____5585
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "extract_namespace",
                                                  (Accumulated
                                                     (PostProcessed
                                                        (pp_lowercase,
                                                          (SimpleStr
                                                             "namespace name")))),
                                                  "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                  :: uu____5551
                                                 in
                                              (FStar_Getopt.noshort,
                                                "extract_module",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "module_name")))),
                                                "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                                :: uu____5537
                                               in
                                            (FStar_Getopt.noshort, "extract",
                                              (Accumulated
                                                 (SimpleStr
                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                              "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                              :: uu____5523
                                             in
                                          uu____5489 :: uu____5509  in
                                        uu____5455 :: uu____5475  in
                                      (FStar_Getopt.noshort, "dump_module",
                                        (Accumulated
                                           (SimpleStr "module_name")), "")
                                        :: uu____5441
                                       in
                                    uu____5407 :: uu____5427  in
                                  uu____5373 :: uu____5393  in
                                uu____5339 :: uu____5359  in
                              (FStar_Getopt.noshort, "dep",
                                (EnumStr ["make"; "graph"; "full"; "raw"]),
                                "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                                :: uu____5325
                               in
                            (FStar_Getopt.noshort, "defensive",
                              (EnumStr ["no"; "warn"; "fail"]),
                              "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                              :: uu____5311
                             in
                          (FStar_Getopt.noshort, "debug_level",
                            (Accumulated
                               (OpenEnumStr
                                  (["Low"; "Medium"; "High"; "Extreme"],
                                    "..."))),
                            "Control the verbosity of debugging info") ::
                            uu____5297
                           in
                        (FStar_Getopt.noshort, "debug",
                          (Accumulated (SimpleStr "module_name")),
                          "Print lots of debugging information while checking module")
                          :: uu____5283
                         in
                      (FStar_Getopt.noshort, "codegen-lib",
                        (Accumulated (SimpleStr "namespace")),
                        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                        :: uu____5269
                       in
                    (FStar_Getopt.noshort, "codegen",
                      (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                      "Generate code for further compilation to executable code, or build a compiler plugin")
                      :: uu____5255
                     in
                  uu____5221 :: uu____5241  in
                uu____5187 :: uu____5207  in
              (FStar_Getopt.noshort, "cache_dir",
                (PostProcessed (pp_validate_dir, (PathStr "dir"))),
                "Read and write .checked and .checked.lax in directory <dir>")
                :: uu____5173
               in
            uu____5139 :: uu____5159  in
          (FStar_Getopt.noshort, "already_cached",
            (Accumulated
               (SimpleStr
                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
            "\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")
            :: uu____5125
           in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____5111
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____5097
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___7_9362  ->
             match uu___7_9362 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____5083

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____9391  ->
    let uu____9394 = specs_with_types ()  in
    FStar_List.map
      (fun uu____9425  ->
         match uu____9425 with
         | (short,long,typ,doc) ->
             let uu____9447 =
               let uu____9461 = arg_spec_of_opt_type long typ  in
               (short, long, uu____9461, doc)  in
             mk_spec uu____9447) uu____9394

let (settable : Prims.string -> Prims.bool) =
  fun uu___8_9476  ->
    match uu___8_9476 with
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
    | uu____9599 -> false
  
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
       (fun uu____9698  ->
          match uu____9698 with
          | (uu____9713,x,uu____9715,uu____9716) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____9791  ->
          match uu____9791 with
          | (uu____9806,x,uu____9808,uu____9809) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____9825  ->
    let uu____9826 = specs ()  in display_usage_aux uu____9826
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____9858 -> true
    | uu____9861 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____9871 -> uu____9871
  
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
        (fun uu___470_9892  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____9909 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____9909
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____9934  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____9940 =
             let uu____9944 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____9944 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____9940)
       in
    let uu____10001 =
      let uu____10005 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____10005
       in
    (res, uu____10001)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____10047  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____10090 = specs ()  in
       FStar_Getopt.parse_cmdline uu____10090 (fun x  -> ())  in
     (let uu____10097 =
        let uu____10103 =
          let uu____10104 = FStar_List.map mk_string old_verify_module  in
          List uu____10104  in
        ("verify_module", uu____10103)  in
      set_option' uu____10097);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____10123 =
        let uu____10125 =
          let uu____10127 =
            let uu____10129 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____10129  in
          (FStar_String.length f1) - uu____10127  in
        uu____10125 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____10123  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____10142 = get_lax ()  in
    if uu____10142
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____10163 = module_name_of_file_name fn  in
    should_verify uu____10163
  
let (module_name_eq : Prims.string -> Prims.string -> Prims.bool) =
  fun m1  ->
    fun m2  -> (FStar_String.lowercase m1) = (FStar_String.lowercase m2)
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____10191 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____10191 (FStar_List.existsb (module_name_eq m))
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____10209 = should_verify m  in
    if uu____10209 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____10226  ->
    let cache_dir =
      let uu____10231 = get_cache_dir ()  in
      match uu____10231 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some c -> [c]  in
    let uu____10245 = get_no_default_includes ()  in
    if uu____10245
    then
      let uu____10251 = get_include ()  in
      FStar_List.append cache_dir uu____10251
    else
      (let lib_paths =
         let uu____10262 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____10262 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = FStar_String.op_Hat fstar_bin_directory "/.."
                in
             let defs = universe_include_path_base_dirs  in
             let uu____10278 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> FStar_String.op_Hat fstar_home x))
                in
             FStar_All.pipe_right uu____10278
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____10305 =
         let uu____10309 =
           let uu____10313 = get_include ()  in
           FStar_List.append uu____10313 ["."]  in
         FStar_List.append lib_paths uu____10309  in
       FStar_List.append cache_dir uu____10305)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____10344 = FStar_Util.smap_try_find file_map filename  in
    match uu____10344 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___521_10375  ->
               match () with
               | () ->
                   let uu____10379 = FStar_Util.is_path_absolute filename  in
                   if uu____10379
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____10395 =
                        let uu____10399 = include_path ()  in
                        FStar_List.rev uu____10399  in
                      FStar_Util.find_map uu____10395
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___520_10427 -> FStar_Pervasives_Native.None  in
        (if FStar_Option.isSome result
         then FStar_Util.smap_add file_map filename result
         else ();
         result)
  
let (prims : unit -> Prims.string) =
  fun uu____10446  ->
    let uu____10447 = get_prims ()  in
    match uu____10447 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____10456 = find_file filename  in
        (match uu____10456 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____10465 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____10465)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____10478  ->
    let uu____10479 = prims ()  in FStar_Util.basename uu____10479
  
let (pervasives : unit -> Prims.string) =
  fun uu____10487  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____10491 = find_file filename  in
    match uu____10491 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____10500 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____10500
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____10510  ->
    let uu____10511 = pervasives ()  in FStar_Util.basename uu____10511
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____10519  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____10523 = find_file filename  in
    match uu____10523 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____10532 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____10532
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____10545 = get_odir ()  in
    match uu____10545 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____10563 = get_cache_dir ()  in
    match uu____10563 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____10572 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____10572
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns  ->
    let cache = FStar_Util.smap_create (Prims.parse_int "31")  in
    let with_cache f s =
      let uu____10694 = FStar_Util.smap_try_find cache s  in
      match uu____10694 with
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
             let uu____10829 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____10829  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____10852 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              let s1 = FStar_Util.trim_string s  in
              if s1 = ""
              then []
              else
                with_cache
                  (fun s2  ->
                     let uu____10920 =
                       FStar_All.pipe_right (FStar_Util.splitlines s2)
                         (FStar_List.concatMap
                            (fun s3  -> FStar_Util.split s3 " "))
                        in
                     FStar_All.pipe_right uu____10920
                       (FStar_List.map parse_one_setting)) s1))
       in
    FStar_All.pipe_right uu____10852 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____10995 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____10995 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____11010  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____11019  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11028  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____11035  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____11042  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____11049  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____11059 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____11070 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____11081 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____11092 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____11101  ->
    let uu____11102 = get_codegen ()  in
    FStar_Util.map_opt uu____11102
      (fun uu___9_11108  ->
         match uu___9_11108 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____11114 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____11127  ->
    let uu____11128 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____11128
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____11154  -> let uu____11155 = get_debug ()  in uu____11155 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____11172 = get_debug ()  in
    FStar_All.pipe_right uu____11172
      (FStar_List.existsb (module_name_eq modul))
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____11197 = get_debug ()  in
       FStar_All.pipe_right uu____11197
         (FStar_List.existsb (module_name_eq modul)))
        && (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____11212  ->
    let uu____11213 = get_defensive ()  in uu____11213 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____11223  ->
    let uu____11224 = get_defensive ()  in uu____11224 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11236  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____11243  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____11250  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____11257  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____11267 = get_dump_module ()  in
    FStar_All.pipe_right uu____11267 (FStar_List.existsb (module_name_eq s))
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____11282  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____11289  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____11299 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____11299
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____11335  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____11343  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____11350  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11359  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____11366  -> get_ide () 
let (print : unit -> Prims.bool) = fun uu____11373  -> get_print () 
let (print_in_place : unit -> Prims.bool) =
  fun uu____11380  -> get_print_in_place () 
let profile : 'a . (unit -> 'a) -> ('a -> Prims.string) -> 'a =
  fun f  ->
    fun msg  ->
      let uu____11411 = get_profile ()  in
      if uu____11411
      then
        let uu____11414 = FStar_Util.record_time f  in
        match uu____11414 with
        | (a,time) ->
            ((let uu____11425 = FStar_Util.string_of_int time  in
              let uu____11427 = msg a  in
              FStar_Util.print2 "Elapsed time %s ms: %s\n" uu____11425
                uu____11427);
             a)
      else f ()
  
let (protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____11438  -> get_protect_top_level_axioms () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____11445  ->
    let uu____11446 = get_initial_fuel ()  in
    let uu____11448 = get_max_fuel ()  in Prims.min uu____11446 uu____11448
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____11456  ->
    let uu____11457 = get_initial_ifuel ()  in
    let uu____11459 = get_max_ifuel ()  in Prims.min uu____11457 uu____11459
  
let (interactive : unit -> Prims.bool) =
  fun uu____11467  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____11474  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____11483  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____11490  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____11497  -> get_log_queries () 
let (keep_query_captions : unit -> Prims.bool) =
  fun uu____11504  -> (log_queries ()) && (get_keep_query_captions ()) 
let (log_types : unit -> Prims.bool) = fun uu____11511  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____11518  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____11525  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____11532  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____11539  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____11545  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____11554  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____11561  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____11571 = get_no_extract ()  in
    FStar_All.pipe_right uu____11571 (FStar_List.existsb (module_name_eq s))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____11586  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____11593  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____11600  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____11607  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11616  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____11623  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____11630  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____11637  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____11644  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____11651  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____11658  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____11665  -> get_print_z3_statistics () 
let (query_stats : unit -> Prims.bool) =
  fun uu____11672  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____11679  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11688  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____11695  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____11702  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____11709  ->
    let uu____11710 = get_smtencoding_nl_arith_repr ()  in
    uu____11710 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____11720  ->
    let uu____11721 = get_smtencoding_nl_arith_repr ()  in
    uu____11721 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____11731  ->
    let uu____11732 = get_smtencoding_nl_arith_repr ()  in
    uu____11732 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____11742  ->
    let uu____11743 = get_smtencoding_l_arith_repr ()  in
    uu____11743 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____11753  ->
    let uu____11754 = get_smtencoding_l_arith_repr ()  in
    uu____11754 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____11764  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____11771  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____11778  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____11785  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____11792  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____11799  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____11806  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____11813  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____11820  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____11827  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____11834  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____11841  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____11848  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____11855  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11864  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____11871  -> get_use_tactics () 
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu____11887  ->
    let uu____11888 = get_using_facts_from ()  in
    match uu____11888 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____11942  ->
    let uu____11943 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____11943
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____11954  ->
    let uu____11955 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____11955 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____11963 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____11974  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____11981  ->
    let uu____11982 = get_smt ()  in
    match uu____11982 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____12000  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____12007  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____12014  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____12021  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____12028  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____12035  ->
    (get_use_two_phase_tc ()) &&
      (let uu____12037 = lax ()  in Prims.op_Negation uu____12037)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____12045  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____12052  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____12059  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____12066  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____12073  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____12090 =
      let uu____12092 = trace_error ()  in Prims.op_Negation uu____12092  in
    if uu____12090
    then
      (push ();
       (let r =
          try
            (fun uu___718_12107  ->
               match () with
               | () -> let uu____12112 = f ()  in FStar_Util.Inr uu____12112)
              ()
          with | uu___717_12114 -> FStar_Util.Inl uu___717_12114  in
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
        | (uu____12195,[]) -> true
        | (m2::ms,p::ps) ->
            (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
        | uu____12228 -> false  in
      let uu____12240 =
        FStar_All.pipe_right setting
          (FStar_Util.try_find
             (fun uu____12282  ->
                match uu____12282 with
                | (path,uu____12293) -> matches_path m_components path))
         in
      match uu____12240 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____12312,flag) -> flag
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____12341 = get_extract ()  in
    match uu____12341 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____12356 =
            let uu____12372 = get_no_extract ()  in
            let uu____12376 = get_extract_namespace ()  in
            let uu____12380 = get_extract_module ()  in
            (uu____12372, uu____12376, uu____12380)  in
          match uu____12356 with
          | ([],[],[]) -> ()
          | uu____12405 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         module_matches_namespace_filter m1 extract_setting)
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____12434 = get_extract_namespace ()  in
          match uu____12434 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____12462 = get_extract_module ()  in
          match uu____12462 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____12484 = no_extract m1  in Prims.op_Negation uu____12484)
          &&
          (let uu____12487 =
             let uu____12498 = get_extract_namespace ()  in
             let uu____12502 = get_extract_module ()  in
             (uu____12498, uu____12502)  in
           (match uu____12487 with
            | ([],[]) -> true
            | uu____12522 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  
let (should_be_already_cached : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____12542 = get_already_cached ()  in
    match uu____12542 with
    | FStar_Pervasives_Native.None  -> false
    | FStar_Pervasives_Native.Some already_cached_setting ->
        module_matches_namespace_filter m already_cached_setting
  
let (error_flags : unit -> error_flag Prims.list) =
  let cache = FStar_Util.smap_create (Prims.parse_int "10")  in
  fun uu____12575  ->
    let we = warn_error ()  in
    let uu____12578 = FStar_Util.smap_try_find cache we  in
    match uu____12578 with
    | FStar_Pervasives_Native.None  ->
        let r = parse_warn_error we  in (FStar_Util.smap_add cache we r; r)
    | FStar_Pervasives_Native.Some r -> r
  