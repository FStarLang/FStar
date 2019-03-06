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
  fun projectee  ->
    match projectee with | Low  -> true | uu____31024 -> false
  
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____31035 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | High  -> true | uu____31046 -> false
  
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____31057 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____31070 -> false
  
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
    match projectee with | Bool _0 -> true | uu____31125 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____31149 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____31173 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____31197 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____31222 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____31247 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _31255  -> Bool _31255 
let (mk_string : Prims.string -> option_val) = fun _31262  -> String _31262 
let (mk_path : Prims.string -> option_val) = fun _31269  -> Path _31269 
let (mk_int : Prims.int -> option_val) = fun _31276  -> Int _31276 
let (mk_list : option_val Prims.list -> option_val) =
  fun _31284  -> List _31284 
type options =
  | Set 
  | Reset 
  | Restore 
let (uu___is_Set : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Set  -> true | uu____31294 -> false
  
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____31305 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____31316 -> false
  
type error_flag =
  | CFatal 
  | CAlwaysError 
  | CError 
  | CWarning 
  | CSilent 
let (uu___is_CFatal : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CFatal  -> true | uu____31327 -> false
  
let (uu___is_CAlwaysError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CAlwaysError  -> true | uu____31338 -> false
  
let (uu___is_CError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CError  -> true | uu____31349 -> false
  
let (uu___is_CWarning : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CWarning  -> true | uu____31360 -> false
  
let (uu___is_CSilent : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CSilent  -> true | uu____31371 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____31385  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____31412  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____31440  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___289_31469  ->
    match uu___289_31469 with
    | Bool b -> b
    | uu____31473 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___290_31482  ->
    match uu___290_31482 with
    | Int b -> b
    | uu____31486 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___291_31495  ->
    match uu___291_31495 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____31501 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___292_31511  ->
    match uu___292_31511 with
    | List ts -> ts
    | uu____31517 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____31528 .
    (option_val -> 'Auu____31528) -> option_val -> 'Auu____31528 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____31546 = as_list' x  in
      FStar_All.pipe_right uu____31546 (FStar_List.map as_t)
  
let as_option :
  'Auu____31560 .
    (option_val -> 'Auu____31560) ->
      option_val -> 'Auu____31560 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___293_31575  ->
      match uu___293_31575 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____31579 = as_t v1  in
          FStar_Pervasives_Native.Some uu____31579
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___294_31588  ->
    match uu___294_31588 with
    | List ls ->
        let uu____31595 =
          FStar_List.map
            (fun l  ->
               let uu____31607 = as_string l  in
               FStar_Util.split uu____31607 ",") ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____31595
    | uu____31619 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let copy_optionstate :
  'Auu____31631 .
    'Auu____31631 FStar_Util.smap -> 'Auu____31631 FStar_Util.smap
  = fun m  -> FStar_Util.smap_copy m 
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (internal_peek : unit -> optionstate) =
  fun uu____31661  ->
    let uu____31662 =
      let uu____31665 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____31665  in
    FStar_List.hd uu____31662
  
let (peek : unit -> optionstate) = fun uu____31704  -> internal_peek () 
let (pop : unit -> unit) =
  fun uu____31710  ->
    let uu____31711 = FStar_ST.op_Bang fstar_options  in
    match uu____31711 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____31746::[] -> failwith "TOO MANY POPS!"
    | uu____31754::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____31796  ->
    let uu____31797 =
      let uu____31802 =
        let uu____31805 =
          let uu____31808 = FStar_ST.op_Bang fstar_options  in
          FStar_List.hd uu____31808  in
        FStar_List.map copy_optionstate uu____31805  in
      let uu____31842 = FStar_ST.op_Bang fstar_options  in uu____31802 ::
        uu____31842
       in
    FStar_ST.op_Colon_Equals fstar_options uu____31797
  
let (internal_pop : unit -> Prims.bool) =
  fun uu____31909  ->
    let curstack =
      let uu____31913 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____31913  in
    match curstack with
    | [] -> failwith "impossible: empty current option stack"
    | uu____31950::[] -> false
    | uu____31952::tl1 ->
        ((let uu____31957 =
            let uu____31962 =
              let uu____31967 = FStar_ST.op_Bang fstar_options  in
              FStar_List.tl uu____31967  in
            tl1 :: uu____31962  in
          FStar_ST.op_Colon_Equals fstar_options uu____31957);
         true)
  
let (internal_push : unit -> unit) =
  fun uu____32036  ->
    let curstack =
      let uu____32040 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____32040  in
    let stack' =
      let uu____32077 =
        let uu____32078 = FStar_List.hd curstack  in
        copy_optionstate uu____32078  in
      uu____32077 :: curstack  in
    let uu____32081 =
      let uu____32086 =
        let uu____32091 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____32091  in
      stack' :: uu____32086  in
    FStar_ST.op_Colon_Equals fstar_options uu____32081
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____32160 = FStar_ST.op_Bang fstar_options  in
    match uu____32160 with
    | [] -> failwith "set on empty option stack"
    | []::uu____32195 -> failwith "set on empty current option stack"
    | (uu____32203::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
  
let (snapshot : unit -> (Prims.int * unit)) =
  fun uu____32253  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____32283 = peek ()  in FStar_Util.smap_add uu____32283 k v1
  
let (set_option' : (Prims.string * option_val) -> unit) =
  fun uu____32296  -> match uu____32296 with | (k,v1) -> set_option k v1 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____32324 =
      let uu____32328 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____32328
       in
    FStar_ST.op_Colon_Equals light_off_files uu____32324
  
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
    let uu____33298 = FStar_ST.op_Bang r  in
    match uu____33298 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some f)
    | uu____33389 -> failwith "Multiple initialization of FStar.Options"  in
  let get1 uu____33410 =
    let uu____33411 = FStar_ST.op_Bang r  in
    match uu____33411 with
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
    let uu____33550 = FStar_Pervasives_Native.snd parse_warn_error_set_get ()
       in
    uu____33550 s
  
let (init : unit -> unit) =
  fun uu____33581  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____33601  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____33674 =
      let uu____33677 = peek ()  in FStar_Util.smap_try_find uu____33677 s
       in
    match uu____33674 with
    | FStar_Pervasives_Native.None  ->
        let uu____33680 =
          let uu____33682 = FStar_String.op_Hat s " not found"  in
          FStar_String.op_Hat "Impossible: option " uu____33682  in
        failwith uu____33680
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____33694 .
    Prims.string -> (option_val -> 'Auu____33694) -> 'Auu____33694
  = fun s  -> fun c  -> let uu____33712 = get_option s  in c uu____33712 
let (get_abort_on : unit -> Prims.int) =
  fun uu____33719  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____33728  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____33739  -> lookup_opt "admit_except" (as_option as_string) 
let (get_already_cached :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____33755  ->
    lookup_opt "already_cached" (as_option (as_list as_string))
  
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____33772  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33783  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____33795  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____33804  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33815  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____33829  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____33843  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____33857  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____33868  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33879  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____33891  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____33900  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____33909  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____33920  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____33932  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____33941  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____33954  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____33973  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____33987  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____33999  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____34008  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____34017  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____34028  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____34040  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____34049  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____34060  -> lookup_opt "include" (as_list as_string) 
let (get_print : unit -> Prims.bool) =
  fun uu____34072  -> lookup_opt "print" as_bool 
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____34081  -> lookup_opt "print_in_place" as_bool 
let (get_profile : unit -> Prims.bool) =
  fun uu____34090  -> lookup_opt "profile" as_bool 
let (get_protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____34099  -> lookup_opt "protect_top_level_axioms" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____34108  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____34117  -> lookup_opt "initial_ifuel" as_int 
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu____34126  -> lookup_opt "keep_query_captions" as_bool 
let (get_lax : unit -> Prims.bool) =
  fun uu____34135  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____34146  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____34158  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____34167  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____34176  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____34185  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____34194  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____34203  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____34212  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____34221  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____34232  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____34244  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____34253  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____34262  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____34271  ->
    lookup_opt "normalize_pure_terms_for_extraction" as_bool
  
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____34282  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____34294  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____34305  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____34317  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____34326  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____34335  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____34344  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____34353  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____34362  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____34371  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____34380  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____34389  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____34400  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____34412  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____34423  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____34435  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____34444  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____34453  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____34462  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____34471  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____34480  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____34489  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____34498  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____34507  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____34516  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____34525  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____34534  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____34543  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____34552  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____34561  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____34570  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____34579  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____34590  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____34602  ->
    let uu____34603 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____34603
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____34617  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____34636  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____34650  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____34664  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____34676  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____34685  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____34696  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____34708  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____34717  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____34726  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____34735  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____34744  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____34753  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____34762  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____34771  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____34780  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____34789  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___295_34798  ->
    match uu___295_34798 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____34819 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____34828 = get_debug_level ()  in
    FStar_All.pipe_right uu____34828
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "<not set>" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____34884  ->
    let uu____34885 =
      let uu____34887 = FStar_ST.op_Bang _version  in
      let uu____34910 = FStar_ST.op_Bang _platform  in
      let uu____34933 = FStar_ST.op_Bang _compiler  in
      let uu____34956 = FStar_ST.op_Bang _date  in
      let uu____34979 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____34887
        uu____34910 uu____34933 uu____34956 uu____34979
       in
    FStar_Util.print_string uu____34885
  
let display_usage_aux :
  'Auu____35010 'Auu____35011 .
    ('Auu____35010 * Prims.string * 'Auu____35011 FStar_Getopt.opt_variant *
      Prims.string) Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____35066  ->
         match uu____35066 with
         | (uu____35079,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____35098 =
                      let uu____35100 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____35100  in
                    FStar_Util.print_string uu____35098
                  else
                    (let uu____35105 =
                       let uu____35107 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____35107 doc  in
                     FStar_Util.print_string uu____35105)
              | FStar_Getopt.OneArg (uu____35110,argname) ->
                  if doc = ""
                  then
                    let uu____35125 =
                      let uu____35127 = FStar_Util.colorize_bold flag  in
                      let uu____35129 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____35127
                        uu____35129
                       in
                    FStar_Util.print_string uu____35125
                  else
                    (let uu____35134 =
                       let uu____35136 = FStar_Util.colorize_bold flag  in
                       let uu____35138 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____35136
                         uu____35138 doc
                        in
                     FStar_Util.print_string uu____35134))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____35173 = o  in
    match uu____35173 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____35215 =
                let uu____35216 = f ()  in set_option name uu____35216  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____35237 = f x  in set_option name uu____35237
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____35264 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____35264  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____35290 =
        let uu____35293 = lookup_opt name as_list'  in
        FStar_List.append uu____35293 [value]  in
      mk_list uu____35290
  
let accumulate_string :
  'Auu____35307 .
    Prims.string -> ('Auu____35307 -> Prims.string) -> 'Auu____35307 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____35332 =
          let uu____35333 =
            let uu____35334 = post_processor value  in mk_string uu____35334
             in
          accumulated_option name uu____35333  in
        set_option name uu____35332
  
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
    match projectee with | Const _0 -> true | uu____35456 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____35477 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____35499 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____35512 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____35536 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____35562 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____35599 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____35650 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____35691 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____35711 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____35738 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____35782 -> true
    | uu____35785 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____35796 -> uu____35796
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___581_35820  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____35822 ->
                      let uu____35824 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____35824 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____35832 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____35832
                  | PathStr uu____35849 -> mk_path str_val
                  | SimpleStr uu____35851 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____35861 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____35878 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____35878
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
            let uu____35898 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____35898
  
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ  ->
    let desc_of_enum cases =
      let uu____35928 =
        let uu____35930 =
          FStar_String.op_Hat (FStar_String.concat "|" cases) "]"  in
        FStar_String.op_Hat "[" uu____35930  in
      FStar_Pervasives_Native.Some uu____35928  in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____35972,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____35982,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____36013 = desc_of_opt_type typ  in
      match uu____36013 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____36021  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____36047 =
      let uu____36049 = as_string s  in FStar_String.lowercase uu____36049
       in
    mk_string uu____36047
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string)
      Prims.list)
  =
  fun uu____36084  ->
    let uu____36098 =
      let uu____36112 =
        let uu____36126 =
          let uu____36140 =
            let uu____36154 =
              let uu____36166 =
                let uu____36167 = mk_bool true  in Const uu____36167  in
              (FStar_Getopt.noshort, "cache_checked_modules", uu____36166,
                "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
               in
            let uu____36174 =
              let uu____36188 =
                let uu____36202 =
                  let uu____36214 =
                    let uu____36215 = mk_bool true  in Const uu____36215  in
                  (FStar_Getopt.noshort, "cache_off", uu____36214,
                    "Do not read or write any .checked files")
                   in
                let uu____36222 =
                  let uu____36236 =
                    let uu____36248 =
                      let uu____36249 = mk_bool true  in Const uu____36249
                       in
                    (FStar_Getopt.noshort, "cmi", uu____36248,
                      "Inline across module interfaces during extraction (aka. cross-module inlining)")
                     in
                  let uu____36256 =
                    let uu____36270 =
                      let uu____36284 =
                        let uu____36298 =
                          let uu____36312 =
                            let uu____36326 =
                              let uu____36340 =
                                let uu____36354 =
                                  let uu____36366 =
                                    let uu____36367 = mk_bool true  in
                                    Const uu____36367  in
                                  (FStar_Getopt.noshort, "detail_errors",
                                    uu____36366,
                                    "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                   in
                                let uu____36374 =
                                  let uu____36388 =
                                    let uu____36400 =
                                      let uu____36401 = mk_bool true  in
                                      Const uu____36401  in
                                    (FStar_Getopt.noshort,
                                      "detail_hint_replay", uu____36400,
                                      "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                     in
                                  let uu____36408 =
                                    let uu____36422 =
                                      let uu____36434 =
                                        let uu____36435 = mk_bool true  in
                                        Const uu____36435  in
                                      (FStar_Getopt.noshort, "doc",
                                        uu____36434,
                                        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                       in
                                    let uu____36442 =
                                      let uu____36456 =
                                        let uu____36470 =
                                          let uu____36482 =
                                            let uu____36483 = mk_bool true
                                               in
                                            Const uu____36483  in
                                          (FStar_Getopt.noshort,
                                            "eager_inference", uu____36482,
                                            "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                           in
                                        let uu____36490 =
                                          let uu____36504 =
                                            let uu____36516 =
                                              let uu____36517 = mk_bool true
                                                 in
                                              Const uu____36517  in
                                            (FStar_Getopt.noshort,
                                              "eager_subtyping", uu____36516,
                                              "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                             in
                                          let uu____36524 =
                                            let uu____36538 =
                                              let uu____36552 =
                                                let uu____36566 =
                                                  let uu____36580 =
                                                    let uu____36592 =
                                                      let uu____36593 =
                                                        mk_bool true  in
                                                      Const uu____36593  in
                                                    (FStar_Getopt.noshort,
                                                      "expose_interfaces",
                                                      uu____36592,
                                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                     in
                                                  let uu____36600 =
                                                    let uu____36614 =
                                                      let uu____36626 =
                                                        let uu____36627 =
                                                          mk_bool true  in
                                                        Const uu____36627  in
                                                      (FStar_Getopt.noshort,
                                                        "hide_uvar_nums",
                                                        uu____36626,
                                                        "Don't print unification variable numbers")
                                                       in
                                                    let uu____36634 =
                                                      let uu____36648 =
                                                        let uu____36662 =
                                                          let uu____36674 =
                                                            let uu____36675 =
                                                              mk_bool true
                                                               in
                                                            Const uu____36675
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "hint_info",
                                                            uu____36674,
                                                            "Print information regarding hints (deprecated; use --query_stats instead)")
                                                           in
                                                        let uu____36682 =
                                                          let uu____36696 =
                                                            let uu____36708 =
                                                              let uu____36709
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____36709
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "in",
                                                              uu____36708,
                                                              "Legacy interactive mode; reads input from stdin")
                                                             in
                                                          let uu____36716 =
                                                            let uu____36730 =
                                                              let uu____36742
                                                                =
                                                                let uu____36743
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____36743
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "ide",
                                                                uu____36742,
                                                                "JSON-based interactive mode for IDEs")
                                                               in
                                                            let uu____36750 =
                                                              let uu____36764
                                                                =
                                                                let uu____36778
                                                                  =
                                                                  let uu____36790
                                                                    =
                                                                    let uu____36791
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36791
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "print",
                                                                    uu____36790,
                                                                    "Parses and prettyprints the files included on the command line")
                                                                   in
                                                                let uu____36798
                                                                  =
                                                                  let uu____36812
                                                                    =
                                                                    let uu____36824
                                                                    =
                                                                    let uu____36825
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36825
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_in_place",
                                                                    uu____36824,
                                                                    "Parses and prettyprints in place the files included on the command line")
                                                                     in
                                                                  let uu____36832
                                                                    =
                                                                    let uu____36846
                                                                    =
                                                                    let uu____36858
                                                                    =
                                                                    let uu____36859
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36859
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "profile",
                                                                    uu____36858,
                                                                    "Prints timing information for various operations in the compiler")
                                                                     in
                                                                    let uu____36866
                                                                    =
                                                                    let uu____36880
                                                                    =
                                                                    let uu____36894
                                                                    =
                                                                    let uu____36908
                                                                    =
                                                                    let uu____36922
                                                                    =
                                                                    let uu____36936
                                                                    =
                                                                    let uu____36948
                                                                    =
                                                                    let uu____36949
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36949
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____36948,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____36956
                                                                    =
                                                                    let uu____36970
                                                                    =
                                                                    let uu____36984
                                                                    =
                                                                    let uu____36996
                                                                    =
                                                                    let uu____36997
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36997
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____36996,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____37004
                                                                    =
                                                                    let uu____37018
                                                                    =
                                                                    let uu____37030
                                                                    =
                                                                    let uu____37031
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37031
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____37030,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____37038
                                                                    =
                                                                    let uu____37052
                                                                    =
                                                                    let uu____37066
                                                                    =
                                                                    let uu____37080
                                                                    =
                                                                    let uu____37094
                                                                    =
                                                                    let uu____37106
                                                                    =
                                                                    let uu____37107
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37107
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____37106,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____37114
                                                                    =
                                                                    let uu____37128
                                                                    =
                                                                    let uu____37142
                                                                    =
                                                                    let uu____37154
                                                                    =
                                                                    let uu____37155
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37155
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____37154,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____37162
                                                                    =
                                                                    let uu____37176
                                                                    =
                                                                    let uu____37190
                                                                    =
                                                                    let uu____37202
                                                                    =
                                                                    let uu____37203
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37203
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____37202,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____37210
                                                                    =
                                                                    let uu____37224
                                                                    =
                                                                    let uu____37236
                                                                    =
                                                                    let uu____37237
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37237
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____37236,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____37244
                                                                    =
                                                                    let uu____37258
                                                                    =
                                                                    let uu____37270
                                                                    =
                                                                    let uu____37271
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37271
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____37270,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____37278
                                                                    =
                                                                    let uu____37292
                                                                    =
                                                                    let uu____37306
                                                                    =
                                                                    let uu____37320
                                                                    =
                                                                    let uu____37332
                                                                    =
                                                                    let uu____37333
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37333
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____37332,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____37340
                                                                    =
                                                                    let uu____37354
                                                                    =
                                                                    let uu____37366
                                                                    =
                                                                    let uu____37367
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37367
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____37366,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____37374
                                                                    =
                                                                    let uu____37388
                                                                    =
                                                                    let uu____37400
                                                                    =
                                                                    let uu____37401
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37401
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____37400,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____37408
                                                                    =
                                                                    let uu____37422
                                                                    =
                                                                    let uu____37434
                                                                    =
                                                                    let uu____37435
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37435
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____37434,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____37442
                                                                    =
                                                                    let uu____37456
                                                                    =
                                                                    let uu____37468
                                                                    =
                                                                    let uu____37469
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37469
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____37468,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____37476
                                                                    =
                                                                    let uu____37490
                                                                    =
                                                                    let uu____37502
                                                                    =
                                                                    let uu____37503
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37503
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____37502,
                                                                    "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)")
                                                                     in
                                                                    let uu____37510
                                                                    =
                                                                    let uu____37524
                                                                    =
                                                                    let uu____37536
                                                                    =
                                                                    let uu____37537
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37537
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____37536,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____37544
                                                                    =
                                                                    let uu____37558
                                                                    =
                                                                    let uu____37570
                                                                    =
                                                                    let uu____37571
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37571
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____37570,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____37578
                                                                    =
                                                                    let uu____37592
                                                                    =
                                                                    let uu____37604
                                                                    =
                                                                    let uu____37605
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37605
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____37604,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____37612
                                                                    =
                                                                    let uu____37626
                                                                    =
                                                                    let uu____37640
                                                                    =
                                                                    let uu____37652
                                                                    =
                                                                    let uu____37653
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37653
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____37652,
                                                                    "Disable all non-critical output")
                                                                     in
                                                                    let uu____37660
                                                                    =
                                                                    let uu____37674
                                                                    =
                                                                    let uu____37688
                                                                    =
                                                                    let uu____37702
                                                                    =
                                                                    let uu____37716
                                                                    =
                                                                    let uu____37730
                                                                    =
                                                                    let uu____37742
                                                                    =
                                                                    let uu____37743
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37743
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____37742,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____37750
                                                                    =
                                                                    let uu____37764
                                                                    =
                                                                    let uu____37776
                                                                    =
                                                                    let uu____37777
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37777
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____37776,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____37784
                                                                    =
                                                                    let uu____37798
                                                                    =
                                                                    let uu____37810
                                                                    =
                                                                    let uu____37811
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37811
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____37810,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____37818
                                                                    =
                                                                    let uu____37832
                                                                    =
                                                                    let uu____37844
                                                                    =
                                                                    let uu____37845
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37845
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____37844,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____37852
                                                                    =
                                                                    let uu____37866
                                                                    =
                                                                    let uu____37880
                                                                    =
                                                                    let uu____37892
                                                                    =
                                                                    let uu____37893
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37893
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____37892,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____37900
                                                                    =
                                                                    let uu____37914
                                                                    =
                                                                    let uu____37928
                                                                    =
                                                                    let uu____37940
                                                                    =
                                                                    let uu____37941
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37941
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____37940,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____37948
                                                                    =
                                                                    let uu____37962
                                                                    =
                                                                    let uu____37974
                                                                    =
                                                                    let uu____37975
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37975
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____37974,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____37982
                                                                    =
                                                                    let uu____37996
                                                                    =
                                                                    let uu____38008
                                                                    =
                                                                    let uu____38009
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38009
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____38008,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____38016
                                                                    =
                                                                    let uu____38030
                                                                    =
                                                                    let uu____38042
                                                                    =
                                                                    let uu____38043
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38043
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____38042,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____38050
                                                                    =
                                                                    let uu____38064
                                                                    =
                                                                    let uu____38076
                                                                    =
                                                                    let uu____38077
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38077
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____38076,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____38084
                                                                    =
                                                                    let uu____38098
                                                                    =
                                                                    let uu____38110
                                                                    =
                                                                    let uu____38111
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38111
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____38110,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____38118
                                                                    =
                                                                    let uu____38132
                                                                    =
                                                                    let uu____38144
                                                                    =
                                                                    let uu____38145
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38145
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____38144,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____38152
                                                                    =
                                                                    let uu____38166
                                                                    =
                                                                    let uu____38178
                                                                    =
                                                                    let uu____38179
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38179
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____38178,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____38186
                                                                    =
                                                                    let uu____38200
                                                                    =
                                                                    let uu____38214
                                                                    =
                                                                    let uu____38226
                                                                    =
                                                                    let uu____38227
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38227
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____38226,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____38234
                                                                    =
                                                                    let uu____38248
                                                                    =
                                                                    let uu____38260
                                                                    =
                                                                    let uu____38261
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38261
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____38260,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____38268
                                                                    =
                                                                    let uu____38282
                                                                    =
                                                                    let uu____38296
                                                                    =
                                                                    let uu____38310
                                                                    =
                                                                    let uu____38324
                                                                    =
                                                                    let uu____38336
                                                                    =
                                                                    let uu____38337
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38337
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____38336,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____38344
                                                                    =
                                                                    let uu____38358
                                                                    =
                                                                    let uu____38370
                                                                    =
                                                                    let uu____38371
                                                                    =
                                                                    let uu____38379
                                                                    =
                                                                    let uu____38380
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38380
                                                                     in
                                                                    ((fun
                                                                    uu____38387
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____38379)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____38371
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____38370,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____38396
                                                                    =
                                                                    let uu____38410
                                                                    =
                                                                    let uu____38422
                                                                    =
                                                                    let uu____38423
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38423
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____38422,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____38430
                                                                    =
                                                                    let uu____38444
                                                                    =
                                                                    let uu____38458
                                                                    =
                                                                    let uu____38470
                                                                    =
                                                                    let uu____38471
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38471
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____38470,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____38478
                                                                    =
                                                                    let uu____38492
                                                                    =
                                                                    let uu____38506
                                                                    =
                                                                    let uu____38520
                                                                    =
                                                                    let uu____38534
                                                                    =
                                                                    let uu____38548
                                                                    =
                                                                    let uu____38560
                                                                    =
                                                                    let uu____38561
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38561
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____38560,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____38568
                                                                    =
                                                                    let uu____38582
                                                                    =
                                                                    let uu____38594
                                                                    =
                                                                    let uu____38595
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38595
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____38594,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____38602
                                                                    =
                                                                    let uu____38616
                                                                    =
                                                                    let uu____38630
                                                                    =
                                                                    let uu____38644
                                                                    =
                                                                    let uu____38658
                                                                    =
                                                                    let uu____38670
                                                                    =
                                                                    let uu____38671
                                                                    =
                                                                    let uu____38679
                                                                    =
                                                                    let uu____38680
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38680
                                                                     in
                                                                    ((fun
                                                                    uu____38686
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____38679)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____38671
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____38670,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____38714
                                                                    =
                                                                    let uu____38728
                                                                    =
                                                                    let uu____38740
                                                                    =
                                                                    let uu____38741
                                                                    =
                                                                    let uu____38749
                                                                    =
                                                                    let uu____38750
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38750
                                                                     in
                                                                    ((fun
                                                                    uu____38756
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____38749)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____38741
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____38740,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____38784
                                                                    =
                                                                    let uu____38798
                                                                    =
                                                                    let uu____38810
                                                                    =
                                                                    let uu____38811
                                                                    =
                                                                    let uu____38819
                                                                    =
                                                                    let uu____38820
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38820
                                                                     in
                                                                    ((fun
                                                                    uu____38827
                                                                     ->
                                                                    (
                                                                    let uu____38829
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____38829);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____38819)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____38811
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____38810,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____38798]
                                                                     in
                                                                    uu____38728
                                                                    ::
                                                                    uu____38784
                                                                     in
                                                                    uu____38658
                                                                    ::
                                                                    uu____38714
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____38644
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____38630
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____38616
                                                                     in
                                                                    uu____38582
                                                                    ::
                                                                    uu____38602
                                                                     in
                                                                    uu____38548
                                                                    ::
                                                                    uu____38568
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____38534
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____38520
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____38506
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____38492
                                                                     in
                                                                    uu____38458
                                                                    ::
                                                                    uu____38478
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____38444
                                                                     in
                                                                    uu____38410
                                                                    ::
                                                                    uu____38430
                                                                     in
                                                                    uu____38358
                                                                    ::
                                                                    uu____38396
                                                                     in
                                                                    uu____38324
                                                                    ::
                                                                    uu____38344
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____38310
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____38296
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____38282
                                                                     in
                                                                    uu____38248
                                                                    ::
                                                                    uu____38268
                                                                     in
                                                                    uu____38214
                                                                    ::
                                                                    uu____38234
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____38200
                                                                     in
                                                                    uu____38166
                                                                    ::
                                                                    uu____38186
                                                                     in
                                                                    uu____38132
                                                                    ::
                                                                    uu____38152
                                                                     in
                                                                    uu____38098
                                                                    ::
                                                                    uu____38118
                                                                     in
                                                                    uu____38064
                                                                    ::
                                                                    uu____38084
                                                                     in
                                                                    uu____38030
                                                                    ::
                                                                    uu____38050
                                                                     in
                                                                    uu____37996
                                                                    ::
                                                                    uu____38016
                                                                     in
                                                                    uu____37962
                                                                    ::
                                                                    uu____37982
                                                                     in
                                                                    uu____37928
                                                                    ::
                                                                    uu____37948
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____37914
                                                                     in
                                                                    uu____37880
                                                                    ::
                                                                    uu____37900
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____37866
                                                                     in
                                                                    uu____37832
                                                                    ::
                                                                    uu____37852
                                                                     in
                                                                    uu____37798
                                                                    ::
                                                                    uu____37818
                                                                     in
                                                                    uu____37764
                                                                    ::
                                                                    uu____37784
                                                                     in
                                                                    uu____37730
                                                                    ::
                                                                    uu____37750
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____37716
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____37702
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____37688
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____37674
                                                                     in
                                                                    uu____37640
                                                                    ::
                                                                    uu____37660
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____37626
                                                                     in
                                                                    uu____37592
                                                                    ::
                                                                    uu____37612
                                                                     in
                                                                    uu____37558
                                                                    ::
                                                                    uu____37578
                                                                     in
                                                                    uu____37524
                                                                    ::
                                                                    uu____37544
                                                                     in
                                                                    uu____37490
                                                                    ::
                                                                    uu____37510
                                                                     in
                                                                    uu____37456
                                                                    ::
                                                                    uu____37476
                                                                     in
                                                                    uu____37422
                                                                    ::
                                                                    uu____37442
                                                                     in
                                                                    uu____37388
                                                                    ::
                                                                    uu____37408
                                                                     in
                                                                    uu____37354
                                                                    ::
                                                                    uu____37374
                                                                     in
                                                                    uu____37320
                                                                    ::
                                                                    uu____37340
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____37306
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____37292
                                                                     in
                                                                    uu____37258
                                                                    ::
                                                                    uu____37278
                                                                     in
                                                                    uu____37224
                                                                    ::
                                                                    uu____37244
                                                                     in
                                                                    uu____37190
                                                                    ::
                                                                    uu____37210
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____37176
                                                                     in
                                                                    uu____37142
                                                                    ::
                                                                    uu____37162
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____37128
                                                                     in
                                                                    uu____37094
                                                                    ::
                                                                    uu____37114
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____37080
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____37066
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____37052
                                                                     in
                                                                    uu____37018
                                                                    ::
                                                                    uu____37038
                                                                     in
                                                                    uu____36984
                                                                    ::
                                                                    uu____37004
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____36970
                                                                     in
                                                                    uu____36936
                                                                    ::
                                                                    uu____36956
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    "Retain comments in the logged SMT queries (requires --log_queries; default true)")
                                                                    ::
                                                                    uu____36922
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____36908
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try initially (default 2)")
                                                                    ::
                                                                    uu____36894
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "protect_top_level_axioms",
                                                                    BoolStr,
                                                                    "Guard nullary top-level symbols in the SMT encoding from provide ambient ground facts (default 'true')")
                                                                    ::
                                                                    uu____36880
                                                                     in
                                                                    uu____36846
                                                                    ::
                                                                    uu____36866
                                                                     in
                                                                  uu____36812
                                                                    ::
                                                                    uu____36832
                                                                   in
                                                                uu____36778
                                                                  ::
                                                                  uu____36798
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "include",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "path")),
                                                                "A directory in which to search for files included on the command line")
                                                                ::
                                                                uu____36764
                                                               in
                                                            uu____36730 ::
                                                              uu____36750
                                                             in
                                                          uu____36696 ::
                                                            uu____36716
                                                           in
                                                        uu____36662 ::
                                                          uu____36682
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "hint_file",
                                                        (PathStr "path"),
                                                        "Read/write hints to <path> (instead of module-specific hints files)")
                                                        :: uu____36648
                                                       in
                                                    uu____36614 ::
                                                      uu____36634
                                                     in
                                                  uu____36580 :: uu____36600
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "extract_namespace",
                                                  (Accumulated
                                                     (PostProcessed
                                                        (pp_lowercase,
                                                          (SimpleStr
                                                             "namespace name")))),
                                                  "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                  :: uu____36566
                                                 in
                                              (FStar_Getopt.noshort,
                                                "extract_module",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "module_name")))),
                                                "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                                :: uu____36552
                                               in
                                            (FStar_Getopt.noshort, "extract",
                                              (Accumulated
                                                 (SimpleStr
                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                              "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                              :: uu____36538
                                             in
                                          uu____36504 :: uu____36524  in
                                        uu____36470 :: uu____36490  in
                                      (FStar_Getopt.noshort, "dump_module",
                                        (Accumulated
                                           (SimpleStr "module_name")), "")
                                        :: uu____36456
                                       in
                                    uu____36422 :: uu____36442  in
                                  uu____36388 :: uu____36408  in
                                uu____36354 :: uu____36374  in
                              (FStar_Getopt.noshort, "dep",
                                (EnumStr ["make"; "graph"; "full"; "raw"]),
                                "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                                :: uu____36340
                               in
                            (FStar_Getopt.noshort, "defensive",
                              (EnumStr ["no"; "warn"; "fail"]),
                              "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                              :: uu____36326
                             in
                          (FStar_Getopt.noshort, "debug_level",
                            (Accumulated
                               (OpenEnumStr
                                  (["Low"; "Medium"; "High"; "Extreme"],
                                    "..."))),
                            "Control the verbosity of debugging info") ::
                            uu____36312
                           in
                        (FStar_Getopt.noshort, "debug",
                          (Accumulated (SimpleStr "module_name")),
                          "Print lots of debugging information while checking module")
                          :: uu____36298
                         in
                      (FStar_Getopt.noshort, "codegen-lib",
                        (Accumulated (SimpleStr "namespace")),
                        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                        :: uu____36284
                       in
                    (FStar_Getopt.noshort, "codegen",
                      (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                      "Generate code for further compilation to executable code, or build a compiler plugin")
                      :: uu____36270
                     in
                  uu____36236 :: uu____36256  in
                uu____36202 :: uu____36222  in
              (FStar_Getopt.noshort, "cache_dir",
                (PostProcessed (pp_validate_dir, (PathStr "dir"))),
                "Read and write .checked and .checked.lax in directory <dir>")
                :: uu____36188
               in
            uu____36154 :: uu____36174  in
          (FStar_Getopt.noshort, "already_cached",
            (Accumulated
               (SimpleStr
                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
            "\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")
            :: uu____36140
           in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____36126
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____36112
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___296_40377  ->
             match uu___296_40377 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____36098

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____40406  ->
    let uu____40409 = specs_with_types ()  in
    FStar_List.map
      (fun uu____40440  ->
         match uu____40440 with
         | (short,long,typ,doc) ->
             let uu____40462 =
               let uu____40476 = arg_spec_of_opt_type long typ  in
               (short, long, uu____40476, doc)  in
             mk_spec uu____40462) uu____40409

let (settable : Prims.string -> Prims.bool) =
  fun uu___297_40491  ->
    match uu___297_40491 with
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
    | uu____40614 -> false
  
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
       (fun uu____40713  ->
          match uu____40713 with
          | (uu____40728,x,uu____40730,uu____40731) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____40806  ->
          match uu____40806 with
          | (uu____40821,x,uu____40823,uu____40824) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____40840  ->
    let uu____40841 = specs ()  in display_usage_aux uu____40841
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____40873 -> true
    | uu____40876 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____40887 -> uu____40887
  
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
        (fun uu___759_40908  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____40925 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____40925
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____40950  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____40956 =
             let uu____40960 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____40960 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____40956)
       in
    let uu____41017 =
      let uu____41021 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____41021
       in
    (res, uu____41017)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____41063  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____41106 = specs ()  in
       FStar_Getopt.parse_cmdline uu____41106 (fun x  -> ())  in
     (let uu____41113 =
        let uu____41119 =
          let uu____41120 = FStar_List.map mk_string old_verify_module  in
          List uu____41120  in
        ("verify_module", uu____41119)  in
      set_option' uu____41113);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____41139 =
        let uu____41141 =
          let uu____41143 =
            let uu____41145 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____41145  in
          (FStar_String.length f1) - uu____41143  in
        uu____41141 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____41139  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____41158 = get_lax ()  in
    if uu____41158
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____41179 = module_name_of_file_name fn  in
    should_verify uu____41179
  
let (module_name_eq : Prims.string -> Prims.string -> Prims.bool) =
  fun m1  ->
    fun m2  -> (FStar_String.lowercase m1) = (FStar_String.lowercase m2)
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____41207 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____41207 (FStar_List.existsb (module_name_eq m))
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____41225 = should_verify m  in
    if uu____41225 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____41242  ->
    let cache_dir =
      let uu____41247 = get_cache_dir ()  in
      match uu____41247 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some c -> [c]  in
    let uu____41261 = get_no_default_includes ()  in
    if uu____41261
    then
      let uu____41267 = get_include ()  in
      FStar_List.append cache_dir uu____41267
    else
      (let lib_paths =
         let uu____41278 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____41278 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = FStar_String.op_Hat fstar_bin_directory "/.."
                in
             let defs = universe_include_path_base_dirs  in
             let uu____41294 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> FStar_String.op_Hat fstar_home x))
                in
             FStar_All.pipe_right uu____41294
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____41321 =
         let uu____41325 =
           let uu____41329 = get_include ()  in
           FStar_List.append uu____41329 ["."]  in
         FStar_List.append lib_paths uu____41325  in
       FStar_List.append cache_dir uu____41321)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____41356 = FStar_Util.smap_try_find file_map filename  in
    match uu____41356 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___810_41378  ->
               match () with
               | () ->
                   let uu____41382 = FStar_Util.is_path_absolute filename  in
                   if uu____41382
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____41398 =
                        let uu____41402 = include_path ()  in
                        FStar_List.rev uu____41402  in
                      FStar_Util.find_map uu____41398
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___809_41430 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____41450  ->
    let uu____41451 = get_prims ()  in
    match uu____41451 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____41460 = find_file filename  in
        (match uu____41460 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____41469 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____41469)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____41482  ->
    let uu____41483 = prims ()  in FStar_Util.basename uu____41483
  
let (pervasives : unit -> Prims.string) =
  fun uu____41491  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____41495 = find_file filename  in
    match uu____41495 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____41504 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____41504
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____41514  ->
    let uu____41515 = pervasives ()  in FStar_Util.basename uu____41515
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____41523  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____41527 = find_file filename  in
    match uu____41527 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____41536 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____41536
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____41549 = get_odir ()  in
    match uu____41549 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____41567 = get_cache_dir ()  in
    match uu____41567 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____41576 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____41576
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns  ->
    let cache = FStar_Util.smap_create (Prims.parse_int "31")  in
    let with_cache f s =
      let uu____41698 = FStar_Util.smap_try_find cache s  in
      match uu____41698 with
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
             let uu____41833 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____41833  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____41856 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              let s1 = FStar_Util.trim_string s  in
              if s1 = ""
              then []
              else
                with_cache
                  (fun s2  ->
                     let uu____41924 =
                       FStar_All.pipe_right (FStar_Util.splitlines s2)
                         (FStar_List.concatMap
                            (fun s3  -> FStar_Util.split s3 " "))
                        in
                     FStar_All.pipe_right uu____41924
                       (FStar_List.map parse_one_setting)) s1))
       in
    FStar_All.pipe_right uu____41856 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____41999 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____41999 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____42014  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____42023  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____42032  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____42039  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____42046  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____42053  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____42063 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____42074 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____42085 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____42096 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____42105  ->
    let uu____42106 = get_codegen ()  in
    FStar_Util.map_opt uu____42106
      (fun uu___298_42112  ->
         match uu___298_42112 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____42118 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____42131  ->
    let uu____42132 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____42132
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____42158  -> let uu____42159 = get_debug ()  in uu____42159 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____42176 = get_debug ()  in
    FStar_All.pipe_right uu____42176
      (FStar_List.existsb (module_name_eq modul))
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____42201 = get_debug ()  in
       FStar_All.pipe_right uu____42201
         (FStar_List.existsb (module_name_eq modul)))
        && (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____42216  ->
    let uu____42217 = get_defensive ()  in uu____42217 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____42227  ->
    let uu____42228 = get_defensive ()  in uu____42228 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____42240  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____42247  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____42254  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____42261  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____42271 = get_dump_module ()  in
    FStar_All.pipe_right uu____42271 (FStar_List.existsb (module_name_eq s))
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____42286  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____42293  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____42303 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____42303
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____42339  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____42347  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____42354  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____42363  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____42370  -> get_ide () 
let (print : unit -> Prims.bool) = fun uu____42377  -> get_print () 
let (print_in_place : unit -> Prims.bool) =
  fun uu____42384  -> get_print_in_place () 
let profile : 'a . (unit -> 'a) -> ('a -> Prims.string) -> 'a =
  fun f  ->
    fun msg  ->
      let uu____42415 = get_profile ()  in
      if uu____42415
      then
        let uu____42418 = FStar_Util.record_time f  in
        match uu____42418 with
        | (a,time) ->
            ((let uu____42429 = FStar_Util.string_of_int time  in
              let uu____42431 = msg a  in
              FStar_Util.print2 "Elapsed time %s ms: %s\n" uu____42429
                uu____42431);
             a)
      else f ()
  
let (protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____42442  -> get_protect_top_level_axioms () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____42449  ->
    let uu____42450 = get_initial_fuel ()  in
    let uu____42452 = get_max_fuel ()  in Prims.min uu____42450 uu____42452
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____42460  ->
    let uu____42461 = get_initial_ifuel ()  in
    let uu____42463 = get_max_ifuel ()  in Prims.min uu____42461 uu____42463
  
let (interactive : unit -> Prims.bool) =
  fun uu____42471  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____42478  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____42487  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____42494  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____42501  -> get_log_queries () 
let (keep_query_captions : unit -> Prims.bool) =
  fun uu____42508  -> (log_queries ()) && (get_keep_query_captions ()) 
let (log_types : unit -> Prims.bool) = fun uu____42515  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____42522  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____42529  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____42536  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____42543  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____42549  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____42558  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____42565  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____42575 = get_no_extract ()  in
    FStar_All.pipe_right uu____42575 (FStar_List.existsb (module_name_eq s))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____42590  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____42597  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____42604  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____42611  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____42620  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____42627  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____42634  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____42641  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____42648  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____42655  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____42662  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____42669  -> get_print_z3_statistics () 
let (query_stats : unit -> Prims.bool) =
  fun uu____42676  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____42683  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____42692  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____42699  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____42706  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____42713  ->
    let uu____42714 = get_smtencoding_nl_arith_repr ()  in
    uu____42714 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____42724  ->
    let uu____42725 = get_smtencoding_nl_arith_repr ()  in
    uu____42725 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____42735  ->
    let uu____42736 = get_smtencoding_nl_arith_repr ()  in
    uu____42736 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____42746  ->
    let uu____42747 = get_smtencoding_l_arith_repr ()  in
    uu____42747 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____42757  ->
    let uu____42758 = get_smtencoding_l_arith_repr ()  in
    uu____42758 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____42768  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____42775  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____42782  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____42789  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____42796  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____42803  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____42810  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____42817  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____42824  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____42831  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____42838  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____42845  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____42852  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____42859  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____42868  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____42875  -> get_use_tactics () 
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu____42891  ->
    let uu____42892 = get_using_facts_from ()  in
    match uu____42892 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____42946  ->
    let uu____42947 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____42947
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____42958  ->
    let uu____42959 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____42959 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____42967 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____42978  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____42985  ->
    let uu____42986 = get_smt ()  in
    match uu____42986 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____43004  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____43011  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____43018  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____43025  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____43032  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____43039  ->
    (get_use_two_phase_tc ()) &&
      (let uu____43041 = lax ()  in Prims.op_Negation uu____43041)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____43049  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____43056  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____43063  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____43070  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____43077  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____43094 =
      let uu____43096 = trace_error ()  in Prims.op_Negation uu____43096  in
    if uu____43094
    then
      (push ();
       (let r =
          try
            (fun uu___1009_43111  ->
               match () with
               | () -> let uu____43116 = f ()  in FStar_Util.Inr uu____43116)
              ()
          with | uu___1008_43118 -> FStar_Util.Inl uu___1008_43118  in
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
        | (uu____43199,[]) -> true
        | (m2::ms,p::ps) ->
            (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
        | uu____43232 -> false  in
      let uu____43244 =
        FStar_All.pipe_right setting
          (FStar_Util.try_find
             (fun uu____43286  ->
                match uu____43286 with
                | (path,uu____43297) -> matches_path m_components path))
         in
      match uu____43244 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____43316,flag) -> flag
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____43345 = get_extract ()  in
    match uu____43345 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____43360 =
            let uu____43376 = get_no_extract ()  in
            let uu____43380 = get_extract_namespace ()  in
            let uu____43384 = get_extract_module ()  in
            (uu____43376, uu____43380, uu____43384)  in
          match uu____43360 with
          | ([],[],[]) -> ()
          | uu____43409 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         module_matches_namespace_filter m1 extract_setting)
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____43438 = get_extract_namespace ()  in
          match uu____43438 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____43466 = get_extract_module ()  in
          match uu____43466 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____43488 = no_extract m1  in Prims.op_Negation uu____43488)
          &&
          (let uu____43491 =
             let uu____43502 = get_extract_namespace ()  in
             let uu____43506 = get_extract_module ()  in
             (uu____43502, uu____43506)  in
           (match uu____43491 with
            | ([],[]) -> true
            | uu____43526 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  
let (should_be_already_cached : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____43546 = get_already_cached ()  in
    match uu____43546 with
    | FStar_Pervasives_Native.None  -> false
    | FStar_Pervasives_Native.Some already_cached_setting ->
        module_matches_namespace_filter m already_cached_setting
  
let (error_flags : unit -> error_flag Prims.list) =
  let cache = FStar_Util.smap_create (Prims.parse_int "10")  in
  fun uu____43579  ->
    let we = warn_error ()  in
    let uu____43582 = FStar_Util.smap_try_find cache we  in
    match uu____43582 with
    | FStar_Pervasives_Native.None  ->
        let r = parse_warn_error we  in (FStar_Util.smap_add cache we r; r)
    | FStar_Pervasives_Native.Some r -> r
  