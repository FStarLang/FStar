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
    match projectee with | Low  -> true | uu____34667 -> false
  
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____34678 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | High  -> true | uu____34689 -> false
  
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____34700 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____34713 -> false
  
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
    match projectee with | Bool _0 -> true | uu____34768 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____34792 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____34816 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____34840 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____34865 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____34890 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _34898  -> Bool _34898 
let (mk_string : Prims.string -> option_val) = fun _34905  -> String _34905 
let (mk_path : Prims.string -> option_val) = fun _34912  -> Path _34912 
let (mk_int : Prims.int -> option_val) = fun _34919  -> Int _34919 
let (mk_list : option_val Prims.list -> option_val) =
  fun _34927  -> List _34927 
type options =
  | Set 
  | Reset 
  | Restore 
let (uu___is_Set : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Set  -> true | uu____34937 -> false
  
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____34948 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____34959 -> false
  
type error_flag =
  | CFatal 
  | CAlwaysError 
  | CError 
  | CWarning 
  | CSilent 
let (uu___is_CFatal : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CFatal  -> true | uu____34970 -> false
  
let (uu___is_CAlwaysError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CAlwaysError  -> true | uu____34981 -> false
  
let (uu___is_CError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CError  -> true | uu____34992 -> false
  
let (uu___is_CWarning : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CWarning  -> true | uu____35003 -> false
  
let (uu___is_CSilent : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CSilent  -> true | uu____35014 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____35039  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____35066  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____35094  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___289_35123  ->
    match uu___289_35123 with
    | Bool b -> b
    | uu____35127 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___290_35136  ->
    match uu___290_35136 with
    | Int b -> b
    | uu____35140 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___291_35149  ->
    match uu___291_35149 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____35155 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___292_35165  ->
    match uu___292_35165 with
    | List ts -> ts
    | uu____35171 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____35182 .
    (option_val -> 'Auu____35182) -> option_val -> 'Auu____35182 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____35200 = as_list' x  in
      FStar_All.pipe_right uu____35200 (FStar_List.map as_t)
  
let as_option :
  'Auu____35214 .
    (option_val -> 'Auu____35214) ->
      option_val -> 'Auu____35214 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___293_35229  ->
      match uu___293_35229 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____35233 = as_t v1  in
          FStar_Pervasives_Native.Some uu____35233
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___294_35242  ->
    match uu___294_35242 with
    | List ls ->
        let uu____35249 =
          FStar_List.map
            (fun l  ->
               let uu____35261 = as_string l  in
               FStar_Util.split uu____35261 ",") ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____35249
    | uu____35273 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let copy_optionstate :
  'Auu____35285 .
    'Auu____35285 FStar_Util.smap -> 'Auu____35285 FStar_Util.smap
  = fun m  -> FStar_Util.smap_copy m 
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (internal_peek : unit -> optionstate) =
  fun uu____35326  ->
    let uu____35327 =
      let uu____35330 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____35330  in
    FStar_List.hd uu____35327
  
let (peek : unit -> optionstate) = fun uu____35369  -> internal_peek () 
let (pop : unit -> unit) =
  fun uu____35375  ->
    let uu____35376 = FStar_ST.op_Bang fstar_options  in
    match uu____35376 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____35411::[] -> failwith "TOO MANY POPS!"
    | uu____35419::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____35461  ->
    let uu____35462 =
      let uu____35467 =
        let uu____35470 =
          let uu____35473 = FStar_ST.op_Bang fstar_options  in
          FStar_List.hd uu____35473  in
        FStar_List.map copy_optionstate uu____35470  in
      let uu____35507 = FStar_ST.op_Bang fstar_options  in uu____35467 ::
        uu____35507
       in
    FStar_ST.op_Colon_Equals fstar_options uu____35462
  
let (internal_pop : unit -> Prims.bool) =
  fun uu____35574  ->
    let curstack =
      let uu____35578 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____35578  in
    match curstack with
    | [] -> failwith "impossible: empty current option stack"
    | uu____35615::[] -> false
    | uu____35617::tl1 ->
        ((let uu____35622 =
            let uu____35627 =
              let uu____35632 = FStar_ST.op_Bang fstar_options  in
              FStar_List.tl uu____35632  in
            tl1 :: uu____35627  in
          FStar_ST.op_Colon_Equals fstar_options uu____35622);
         true)
  
let (internal_push : unit -> unit) =
  fun uu____35701  ->
    let curstack =
      let uu____35705 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____35705  in
    let stack' =
      let uu____35742 =
        let uu____35743 = FStar_List.hd curstack  in
        copy_optionstate uu____35743  in
      uu____35742 :: curstack  in
    let uu____35746 =
      let uu____35751 =
        let uu____35756 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____35756  in
      stack' :: uu____35751  in
    FStar_ST.op_Colon_Equals fstar_options uu____35746
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____35825 = FStar_ST.op_Bang fstar_options  in
    match uu____35825 with
    | [] -> failwith "set on empty option stack"
    | []::uu____35860 -> failwith "set on empty current option stack"
    | (uu____35868::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
  
let (snapshot : unit -> (Prims.int * unit)) =
  fun uu____35918  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____35948 = peek ()  in FStar_Util.smap_add uu____35948 k v1
  
let (set_option' : (Prims.string * option_val) -> unit) =
  fun uu____35961  -> match uu____35961 with | (k,v1) -> set_option k v1 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____36000 =
      let uu____36004 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____36004
       in
    FStar_ST.op_Colon_Equals light_off_files uu____36000
  
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
    let uu____36974 = FStar_ST.op_Bang r  in
    match uu____36974 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some f)
    | uu____37109 -> failwith "Multiple initialization of FStar.Options"  in
  let get1 uu____37130 =
    let uu____37131 = FStar_ST.op_Bang r  in
    match uu____37131 with
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
    let uu____37292 = FStar_Pervasives_Native.snd parse_warn_error_set_get ()
       in
    uu____37292 s
  
let (init : unit -> unit) =
  fun uu____37323  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____37343  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____37416 =
      let uu____37419 = peek ()  in FStar_Util.smap_try_find uu____37419 s
       in
    match uu____37416 with
    | FStar_Pervasives_Native.None  ->
        let uu____37422 =
          let uu____37424 = FStar_String.op_Hat s " not found"  in
          FStar_String.op_Hat "Impossible: option " uu____37424  in
        failwith uu____37422
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____37436 .
    Prims.string -> (option_val -> 'Auu____37436) -> 'Auu____37436
  = fun s  -> fun c  -> let uu____37454 = get_option s  in c uu____37454 
let (get_abort_on : unit -> Prims.int) =
  fun uu____37461  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____37470  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____37481  -> lookup_opt "admit_except" (as_option as_string) 
let (get_already_cached :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____37497  ->
    lookup_opt "already_cached" (as_option (as_list as_string))
  
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____37514  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37525  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____37537  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____37546  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37557  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____37571  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____37585  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____37599  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____37610  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37621  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____37633  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____37642  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____37651  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____37662  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____37674  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____37683  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____37696  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____37715  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____37729  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____37741  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____37750  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____37759  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37770  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____37782  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____37791  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____37802  -> lookup_opt "include" (as_list as_string) 
let (get_print : unit -> Prims.bool) =
  fun uu____37814  -> lookup_opt "print" as_bool 
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____37823  -> lookup_opt "print_in_place" as_bool 
let (get_profile : unit -> Prims.bool) =
  fun uu____37832  -> lookup_opt "profile" as_bool 
let (get_protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____37841  -> lookup_opt "protect_top_level_axioms" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____37850  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____37859  -> lookup_opt "initial_ifuel" as_int 
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu____37868  -> lookup_opt "keep_query_captions" as_bool 
let (get_lax : unit -> Prims.bool) =
  fun uu____37877  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____37888  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____37900  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____37909  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____37918  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____37927  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____37936  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____37945  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____37954  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____37963  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____37974  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____37986  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____37995  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____38004  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____38013  ->
    lookup_opt "normalize_pure_terms_for_extraction" as_bool
  
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38024  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____38036  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38047  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____38059  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____38068  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____38077  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____38086  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____38095  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____38104  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____38113  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____38122  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____38131  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38142  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____38154  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38165  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____38177  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____38186  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____38195  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____38204  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____38213  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____38222  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____38231  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____38240  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____38249  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____38258  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____38267  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____38276  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____38285  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____38294  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____38303  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____38312  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____38321  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38332  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____38344  ->
    let uu____38345 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____38345
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____38359  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38378  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____38392  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____38406  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____38418  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____38427  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____38438  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____38450  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____38459  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____38468  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____38477  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____38486  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____38495  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____38504  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____38513  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____38522  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____38531  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___295_38540  ->
    match uu___295_38540 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____38561 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____38570 = get_debug_level ()  in
    FStar_All.pipe_right uu____38570
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "<not set>" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____38736  ->
    let uu____38737 =
      let uu____38739 = FStar_ST.op_Bang _version  in
      let uu____38762 = FStar_ST.op_Bang _platform  in
      let uu____38785 = FStar_ST.op_Bang _compiler  in
      let uu____38808 = FStar_ST.op_Bang _date  in
      let uu____38831 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____38739
        uu____38762 uu____38785 uu____38808 uu____38831
       in
    FStar_Util.print_string uu____38737
  
let display_usage_aux :
  'Auu____38862 'Auu____38863 .
    ('Auu____38862 * Prims.string * 'Auu____38863 FStar_Getopt.opt_variant *
      Prims.string) Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____38918  ->
         match uu____38918 with
         | (uu____38931,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____38950 =
                      let uu____38952 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____38952  in
                    FStar_Util.print_string uu____38950
                  else
                    (let uu____38957 =
                       let uu____38959 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____38959 doc  in
                     FStar_Util.print_string uu____38957)
              | FStar_Getopt.OneArg (uu____38962,argname) ->
                  if doc = ""
                  then
                    let uu____38977 =
                      let uu____38979 = FStar_Util.colorize_bold flag  in
                      let uu____38981 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____38979
                        uu____38981
                       in
                    FStar_Util.print_string uu____38977
                  else
                    (let uu____38986 =
                       let uu____38988 = FStar_Util.colorize_bold flag  in
                       let uu____38990 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____38988
                         uu____38990 doc
                        in
                     FStar_Util.print_string uu____38986))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____39025 = o  in
    match uu____39025 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____39067 =
                let uu____39068 = f ()  in set_option name uu____39068  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____39089 = f x  in set_option name uu____39089
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____39116 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____39116  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____39142 =
        let uu____39145 = lookup_opt name as_list'  in
        FStar_List.append uu____39145 [value]  in
      mk_list uu____39142
  
let accumulate_string :
  'Auu____39159 .
    Prims.string -> ('Auu____39159 -> Prims.string) -> 'Auu____39159 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____39184 =
          let uu____39185 =
            let uu____39186 = post_processor value  in mk_string uu____39186
             in
          accumulated_option name uu____39185  in
        set_option name uu____39184
  
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
    match projectee with | Const _0 -> true | uu____39308 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____39329 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____39351 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____39364 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____39388 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____39414 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____39451 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____39502 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____39543 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____39563 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____39590 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____39634 -> true
    | uu____39637 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____39648 -> uu____39648
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___581_39672  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____39674 ->
                      let uu____39676 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____39676 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____39684 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____39684
                  | PathStr uu____39701 -> mk_path str_val
                  | SimpleStr uu____39703 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____39713 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____39730 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____39730
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
            let uu____39750 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____39750
  
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ  ->
    let desc_of_enum cases =
      let uu____39780 =
        let uu____39782 =
          FStar_String.op_Hat (FStar_String.concat "|" cases) "]"  in
        FStar_String.op_Hat "[" uu____39782  in
      FStar_Pervasives_Native.Some uu____39780  in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____39824,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____39834,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____39865 = desc_of_opt_type typ  in
      match uu____39865 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____39873  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____39899 =
      let uu____39901 = as_string s  in FStar_String.lowercase uu____39901
       in
    mk_string uu____39899
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string)
      Prims.list)
  =
  fun uu____39958  ->
    let uu____39972 =
      let uu____39986 =
        let uu____40000 =
          let uu____40014 =
            let uu____40028 =
              let uu____40040 =
                let uu____40041 = mk_bool true  in Const uu____40041  in
              (FStar_Getopt.noshort, "cache_checked_modules", uu____40040,
                "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
               in
            let uu____40048 =
              let uu____40062 =
                let uu____40076 =
                  let uu____40088 =
                    let uu____40089 = mk_bool true  in Const uu____40089  in
                  (FStar_Getopt.noshort, "cache_off", uu____40088,
                    "Do not read or write any .checked files")
                   in
                let uu____40096 =
                  let uu____40110 =
                    let uu____40122 =
                      let uu____40123 = mk_bool true  in Const uu____40123
                       in
                    (FStar_Getopt.noshort, "cmi", uu____40122,
                      "Inline across module interfaces during extraction (aka. cross-module inlining)")
                     in
                  let uu____40130 =
                    let uu____40144 =
                      let uu____40158 =
                        let uu____40172 =
                          let uu____40186 =
                            let uu____40200 =
                              let uu____40214 =
                                let uu____40228 =
                                  let uu____40240 =
                                    let uu____40241 = mk_bool true  in
                                    Const uu____40241  in
                                  (FStar_Getopt.noshort, "detail_errors",
                                    uu____40240,
                                    "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                   in
                                let uu____40248 =
                                  let uu____40262 =
                                    let uu____40274 =
                                      let uu____40275 = mk_bool true  in
                                      Const uu____40275  in
                                    (FStar_Getopt.noshort,
                                      "detail_hint_replay", uu____40274,
                                      "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                     in
                                  let uu____40282 =
                                    let uu____40296 =
                                      let uu____40308 =
                                        let uu____40309 = mk_bool true  in
                                        Const uu____40309  in
                                      (FStar_Getopt.noshort, "doc",
                                        uu____40308,
                                        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                       in
                                    let uu____40316 =
                                      let uu____40330 =
                                        let uu____40344 =
                                          let uu____40356 =
                                            let uu____40357 = mk_bool true
                                               in
                                            Const uu____40357  in
                                          (FStar_Getopt.noshort,
                                            "eager_inference", uu____40356,
                                            "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                           in
                                        let uu____40364 =
                                          let uu____40378 =
                                            let uu____40390 =
                                              let uu____40391 = mk_bool true
                                                 in
                                              Const uu____40391  in
                                            (FStar_Getopt.noshort,
                                              "eager_subtyping", uu____40390,
                                              "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                             in
                                          let uu____40398 =
                                            let uu____40412 =
                                              let uu____40426 =
                                                let uu____40440 =
                                                  let uu____40454 =
                                                    let uu____40466 =
                                                      let uu____40467 =
                                                        mk_bool true  in
                                                      Const uu____40467  in
                                                    (FStar_Getopt.noshort,
                                                      "expose_interfaces",
                                                      uu____40466,
                                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                     in
                                                  let uu____40474 =
                                                    let uu____40488 =
                                                      let uu____40500 =
                                                        let uu____40501 =
                                                          mk_bool true  in
                                                        Const uu____40501  in
                                                      (FStar_Getopt.noshort,
                                                        "hide_uvar_nums",
                                                        uu____40500,
                                                        "Don't print unification variable numbers")
                                                       in
                                                    let uu____40508 =
                                                      let uu____40522 =
                                                        let uu____40536 =
                                                          let uu____40548 =
                                                            let uu____40549 =
                                                              mk_bool true
                                                               in
                                                            Const uu____40549
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "hint_info",
                                                            uu____40548,
                                                            "Print information regarding hints (deprecated; use --query_stats instead)")
                                                           in
                                                        let uu____40556 =
                                                          let uu____40570 =
                                                            let uu____40582 =
                                                              let uu____40583
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____40583
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "in",
                                                              uu____40582,
                                                              "Legacy interactive mode; reads input from stdin")
                                                             in
                                                          let uu____40590 =
                                                            let uu____40604 =
                                                              let uu____40616
                                                                =
                                                                let uu____40617
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____40617
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "ide",
                                                                uu____40616,
                                                                "JSON-based interactive mode for IDEs")
                                                               in
                                                            let uu____40624 =
                                                              let uu____40638
                                                                =
                                                                let uu____40652
                                                                  =
                                                                  let uu____40664
                                                                    =
                                                                    let uu____40665
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40665
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "print",
                                                                    uu____40664,
                                                                    "Parses and prettyprints the files included on the command line")
                                                                   in
                                                                let uu____40672
                                                                  =
                                                                  let uu____40686
                                                                    =
                                                                    let uu____40698
                                                                    =
                                                                    let uu____40699
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40699
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_in_place",
                                                                    uu____40698,
                                                                    "Parses and prettyprints in place the files included on the command line")
                                                                     in
                                                                  let uu____40706
                                                                    =
                                                                    let uu____40720
                                                                    =
                                                                    let uu____40732
                                                                    =
                                                                    let uu____40733
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40733
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "profile",
                                                                    uu____40732,
                                                                    "Prints timing information for various operations in the compiler")
                                                                     in
                                                                    let uu____40740
                                                                    =
                                                                    let uu____40754
                                                                    =
                                                                    let uu____40768
                                                                    =
                                                                    let uu____40782
                                                                    =
                                                                    let uu____40796
                                                                    =
                                                                    let uu____40810
                                                                    =
                                                                    let uu____40822
                                                                    =
                                                                    let uu____40823
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40823
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____40822,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____40830
                                                                    =
                                                                    let uu____40844
                                                                    =
                                                                    let uu____40858
                                                                    =
                                                                    let uu____40870
                                                                    =
                                                                    let uu____40871
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40871
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____40870,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____40878
                                                                    =
                                                                    let uu____40892
                                                                    =
                                                                    let uu____40904
                                                                    =
                                                                    let uu____40905
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40905
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____40904,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____40912
                                                                    =
                                                                    let uu____40926
                                                                    =
                                                                    let uu____40940
                                                                    =
                                                                    let uu____40954
                                                                    =
                                                                    let uu____40968
                                                                    =
                                                                    let uu____40980
                                                                    =
                                                                    let uu____40981
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40981
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____40980,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____40988
                                                                    =
                                                                    let uu____41002
                                                                    =
                                                                    let uu____41016
                                                                    =
                                                                    let uu____41028
                                                                    =
                                                                    let uu____41029
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41029
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____41028,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____41036
                                                                    =
                                                                    let uu____41050
                                                                    =
                                                                    let uu____41064
                                                                    =
                                                                    let uu____41076
                                                                    =
                                                                    let uu____41077
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41077
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____41076,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____41084
                                                                    =
                                                                    let uu____41098
                                                                    =
                                                                    let uu____41110
                                                                    =
                                                                    let uu____41111
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41111
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____41110,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____41118
                                                                    =
                                                                    let uu____41132
                                                                    =
                                                                    let uu____41144
                                                                    =
                                                                    let uu____41145
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41145
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____41144,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____41152
                                                                    =
                                                                    let uu____41166
                                                                    =
                                                                    let uu____41180
                                                                    =
                                                                    let uu____41194
                                                                    =
                                                                    let uu____41206
                                                                    =
                                                                    let uu____41207
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41207
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____41206,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____41214
                                                                    =
                                                                    let uu____41228
                                                                    =
                                                                    let uu____41240
                                                                    =
                                                                    let uu____41241
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41241
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____41240,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____41248
                                                                    =
                                                                    let uu____41262
                                                                    =
                                                                    let uu____41274
                                                                    =
                                                                    let uu____41275
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41275
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____41274,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____41282
                                                                    =
                                                                    let uu____41296
                                                                    =
                                                                    let uu____41308
                                                                    =
                                                                    let uu____41309
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41309
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____41308,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____41316
                                                                    =
                                                                    let uu____41330
                                                                    =
                                                                    let uu____41342
                                                                    =
                                                                    let uu____41343
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41343
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____41342,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____41350
                                                                    =
                                                                    let uu____41364
                                                                    =
                                                                    let uu____41376
                                                                    =
                                                                    let uu____41377
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41377
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____41376,
                                                                    "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)")
                                                                     in
                                                                    let uu____41384
                                                                    =
                                                                    let uu____41398
                                                                    =
                                                                    let uu____41410
                                                                    =
                                                                    let uu____41411
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41411
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____41410,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____41418
                                                                    =
                                                                    let uu____41432
                                                                    =
                                                                    let uu____41444
                                                                    =
                                                                    let uu____41445
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41445
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____41444,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____41452
                                                                    =
                                                                    let uu____41466
                                                                    =
                                                                    let uu____41478
                                                                    =
                                                                    let uu____41479
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41479
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____41478,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____41486
                                                                    =
                                                                    let uu____41500
                                                                    =
                                                                    let uu____41514
                                                                    =
                                                                    let uu____41526
                                                                    =
                                                                    let uu____41527
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41527
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____41526,
                                                                    "Disable all non-critical output")
                                                                     in
                                                                    let uu____41534
                                                                    =
                                                                    let uu____41548
                                                                    =
                                                                    let uu____41562
                                                                    =
                                                                    let uu____41576
                                                                    =
                                                                    let uu____41590
                                                                    =
                                                                    let uu____41604
                                                                    =
                                                                    let uu____41616
                                                                    =
                                                                    let uu____41617
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41617
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____41616,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____41624
                                                                    =
                                                                    let uu____41638
                                                                    =
                                                                    let uu____41650
                                                                    =
                                                                    let uu____41651
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41651
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____41650,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____41658
                                                                    =
                                                                    let uu____41672
                                                                    =
                                                                    let uu____41684
                                                                    =
                                                                    let uu____41685
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41685
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____41684,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____41692
                                                                    =
                                                                    let uu____41706
                                                                    =
                                                                    let uu____41718
                                                                    =
                                                                    let uu____41719
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41719
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____41718,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____41726
                                                                    =
                                                                    let uu____41740
                                                                    =
                                                                    let uu____41754
                                                                    =
                                                                    let uu____41766
                                                                    =
                                                                    let uu____41767
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41767
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____41766,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____41774
                                                                    =
                                                                    let uu____41788
                                                                    =
                                                                    let uu____41802
                                                                    =
                                                                    let uu____41814
                                                                    =
                                                                    let uu____41815
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41815
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____41814,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____41822
                                                                    =
                                                                    let uu____41836
                                                                    =
                                                                    let uu____41848
                                                                    =
                                                                    let uu____41849
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41849
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____41848,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____41856
                                                                    =
                                                                    let uu____41870
                                                                    =
                                                                    let uu____41882
                                                                    =
                                                                    let uu____41883
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41883
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____41882,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____41890
                                                                    =
                                                                    let uu____41904
                                                                    =
                                                                    let uu____41916
                                                                    =
                                                                    let uu____41917
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41917
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____41916,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____41924
                                                                    =
                                                                    let uu____41938
                                                                    =
                                                                    let uu____41950
                                                                    =
                                                                    let uu____41951
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41951
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____41950,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____41958
                                                                    =
                                                                    let uu____41972
                                                                    =
                                                                    let uu____41984
                                                                    =
                                                                    let uu____41985
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41985
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____41984,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____41992
                                                                    =
                                                                    let uu____42006
                                                                    =
                                                                    let uu____42018
                                                                    =
                                                                    let uu____42019
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42019
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____42018,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____42026
                                                                    =
                                                                    let uu____42040
                                                                    =
                                                                    let uu____42052
                                                                    =
                                                                    let uu____42053
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42053
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____42052,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____42060
                                                                    =
                                                                    let uu____42074
                                                                    =
                                                                    let uu____42088
                                                                    =
                                                                    let uu____42100
                                                                    =
                                                                    let uu____42101
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42101
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____42100,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____42108
                                                                    =
                                                                    let uu____42122
                                                                    =
                                                                    let uu____42134
                                                                    =
                                                                    let uu____42135
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42135
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____42134,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____42142
                                                                    =
                                                                    let uu____42156
                                                                    =
                                                                    let uu____42170
                                                                    =
                                                                    let uu____42184
                                                                    =
                                                                    let uu____42198
                                                                    =
                                                                    let uu____42210
                                                                    =
                                                                    let uu____42211
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42211
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____42210,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____42218
                                                                    =
                                                                    let uu____42232
                                                                    =
                                                                    let uu____42244
                                                                    =
                                                                    let uu____42245
                                                                    =
                                                                    let uu____42253
                                                                    =
                                                                    let uu____42254
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42254
                                                                     in
                                                                    ((fun
                                                                    uu____42261
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____42253)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42245
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____42244,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____42270
                                                                    =
                                                                    let uu____42284
                                                                    =
                                                                    let uu____42296
                                                                    =
                                                                    let uu____42297
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42297
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____42296,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____42304
                                                                    =
                                                                    let uu____42318
                                                                    =
                                                                    let uu____42332
                                                                    =
                                                                    let uu____42344
                                                                    =
                                                                    let uu____42345
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42345
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____42344,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____42352
                                                                    =
                                                                    let uu____42366
                                                                    =
                                                                    let uu____42380
                                                                    =
                                                                    let uu____42394
                                                                    =
                                                                    let uu____42408
                                                                    =
                                                                    let uu____42422
                                                                    =
                                                                    let uu____42434
                                                                    =
                                                                    let uu____42435
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42435
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____42434,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____42442
                                                                    =
                                                                    let uu____42456
                                                                    =
                                                                    let uu____42468
                                                                    =
                                                                    let uu____42469
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42469
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____42468,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____42476
                                                                    =
                                                                    let uu____42490
                                                                    =
                                                                    let uu____42504
                                                                    =
                                                                    let uu____42518
                                                                    =
                                                                    let uu____42532
                                                                    =
                                                                    let uu____42544
                                                                    =
                                                                    let uu____42545
                                                                    =
                                                                    let uu____42553
                                                                    =
                                                                    let uu____42554
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42554
                                                                     in
                                                                    ((fun
                                                                    uu____42560
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____42553)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42545
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____42544,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____42588
                                                                    =
                                                                    let uu____42602
                                                                    =
                                                                    let uu____42614
                                                                    =
                                                                    let uu____42615
                                                                    =
                                                                    let uu____42623
                                                                    =
                                                                    let uu____42624
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42624
                                                                     in
                                                                    ((fun
                                                                    uu____42630
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____42623)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42615
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____42614,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____42658
                                                                    =
                                                                    let uu____42672
                                                                    =
                                                                    let uu____42684
                                                                    =
                                                                    let uu____42685
                                                                    =
                                                                    let uu____42693
                                                                    =
                                                                    let uu____42694
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42694
                                                                     in
                                                                    ((fun
                                                                    uu____42701
                                                                     ->
                                                                    (
                                                                    let uu____42703
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____42703);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____42693)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42685
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____42684,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____42672]
                                                                     in
                                                                    uu____42602
                                                                    ::
                                                                    uu____42658
                                                                     in
                                                                    uu____42532
                                                                    ::
                                                                    uu____42588
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____42518
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____42504
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____42490
                                                                     in
                                                                    uu____42456
                                                                    ::
                                                                    uu____42476
                                                                     in
                                                                    uu____42422
                                                                    ::
                                                                    uu____42442
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____42408
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____42394
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____42380
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____42366
                                                                     in
                                                                    uu____42332
                                                                    ::
                                                                    uu____42352
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____42318
                                                                     in
                                                                    uu____42284
                                                                    ::
                                                                    uu____42304
                                                                     in
                                                                    uu____42232
                                                                    ::
                                                                    uu____42270
                                                                     in
                                                                    uu____42198
                                                                    ::
                                                                    uu____42218
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____42184
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____42170
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____42156
                                                                     in
                                                                    uu____42122
                                                                    ::
                                                                    uu____42142
                                                                     in
                                                                    uu____42088
                                                                    ::
                                                                    uu____42108
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____42074
                                                                     in
                                                                    uu____42040
                                                                    ::
                                                                    uu____42060
                                                                     in
                                                                    uu____42006
                                                                    ::
                                                                    uu____42026
                                                                     in
                                                                    uu____41972
                                                                    ::
                                                                    uu____41992
                                                                     in
                                                                    uu____41938
                                                                    ::
                                                                    uu____41958
                                                                     in
                                                                    uu____41904
                                                                    ::
                                                                    uu____41924
                                                                     in
                                                                    uu____41870
                                                                    ::
                                                                    uu____41890
                                                                     in
                                                                    uu____41836
                                                                    ::
                                                                    uu____41856
                                                                     in
                                                                    uu____41802
                                                                    ::
                                                                    uu____41822
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____41788
                                                                     in
                                                                    uu____41754
                                                                    ::
                                                                    uu____41774
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____41740
                                                                     in
                                                                    uu____41706
                                                                    ::
                                                                    uu____41726
                                                                     in
                                                                    uu____41672
                                                                    ::
                                                                    uu____41692
                                                                     in
                                                                    uu____41638
                                                                    ::
                                                                    uu____41658
                                                                     in
                                                                    uu____41604
                                                                    ::
                                                                    uu____41624
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____41590
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____41576
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____41562
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____41548
                                                                     in
                                                                    uu____41514
                                                                    ::
                                                                    uu____41534
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____41500
                                                                     in
                                                                    uu____41466
                                                                    ::
                                                                    uu____41486
                                                                     in
                                                                    uu____41432
                                                                    ::
                                                                    uu____41452
                                                                     in
                                                                    uu____41398
                                                                    ::
                                                                    uu____41418
                                                                     in
                                                                    uu____41364
                                                                    ::
                                                                    uu____41384
                                                                     in
                                                                    uu____41330
                                                                    ::
                                                                    uu____41350
                                                                     in
                                                                    uu____41296
                                                                    ::
                                                                    uu____41316
                                                                     in
                                                                    uu____41262
                                                                    ::
                                                                    uu____41282
                                                                     in
                                                                    uu____41228
                                                                    ::
                                                                    uu____41248
                                                                     in
                                                                    uu____41194
                                                                    ::
                                                                    uu____41214
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____41180
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____41166
                                                                     in
                                                                    uu____41132
                                                                    ::
                                                                    uu____41152
                                                                     in
                                                                    uu____41098
                                                                    ::
                                                                    uu____41118
                                                                     in
                                                                    uu____41064
                                                                    ::
                                                                    uu____41084
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____41050
                                                                     in
                                                                    uu____41016
                                                                    ::
                                                                    uu____41036
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____41002
                                                                     in
                                                                    uu____40968
                                                                    ::
                                                                    uu____40988
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____40954
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____40940
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____40926
                                                                     in
                                                                    uu____40892
                                                                    ::
                                                                    uu____40912
                                                                     in
                                                                    uu____40858
                                                                    ::
                                                                    uu____40878
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____40844
                                                                     in
                                                                    uu____40810
                                                                    ::
                                                                    uu____40830
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    "Retain comments in the logged SMT queries (requires --log_queries; default true)")
                                                                    ::
                                                                    uu____40796
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____40782
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try initially (default 2)")
                                                                    ::
                                                                    uu____40768
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "protect_top_level_axioms",
                                                                    BoolStr,
                                                                    "Guard nullary top-level symbols in the SMT encoding from provide ambient ground facts (default 'true')")
                                                                    ::
                                                                    uu____40754
                                                                     in
                                                                    uu____40720
                                                                    ::
                                                                    uu____40740
                                                                     in
                                                                  uu____40686
                                                                    ::
                                                                    uu____40706
                                                                   in
                                                                uu____40652
                                                                  ::
                                                                  uu____40672
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "include",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "path")),
                                                                "A directory in which to search for files included on the command line")
                                                                ::
                                                                uu____40638
                                                               in
                                                            uu____40604 ::
                                                              uu____40624
                                                             in
                                                          uu____40570 ::
                                                            uu____40590
                                                           in
                                                        uu____40536 ::
                                                          uu____40556
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "hint_file",
                                                        (PathStr "path"),
                                                        "Read/write hints to <path> (instead of module-specific hints files)")
                                                        :: uu____40522
                                                       in
                                                    uu____40488 ::
                                                      uu____40508
                                                     in
                                                  uu____40454 :: uu____40474
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "extract_namespace",
                                                  (Accumulated
                                                     (PostProcessed
                                                        (pp_lowercase,
                                                          (SimpleStr
                                                             "namespace name")))),
                                                  "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                  :: uu____40440
                                                 in
                                              (FStar_Getopt.noshort,
                                                "extract_module",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "module_name")))),
                                                "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                                :: uu____40426
                                               in
                                            (FStar_Getopt.noshort, "extract",
                                              (Accumulated
                                                 (SimpleStr
                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                              "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                              :: uu____40412
                                             in
                                          uu____40378 :: uu____40398  in
                                        uu____40344 :: uu____40364  in
                                      (FStar_Getopt.noshort, "dump_module",
                                        (Accumulated
                                           (SimpleStr "module_name")), "")
                                        :: uu____40330
                                       in
                                    uu____40296 :: uu____40316  in
                                  uu____40262 :: uu____40282  in
                                uu____40228 :: uu____40248  in
                              (FStar_Getopt.noshort, "dep",
                                (EnumStr ["make"; "graph"; "full"; "raw"]),
                                "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                                :: uu____40214
                               in
                            (FStar_Getopt.noshort, "defensive",
                              (EnumStr ["no"; "warn"; "fail"]),
                              "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                              :: uu____40200
                             in
                          (FStar_Getopt.noshort, "debug_level",
                            (Accumulated
                               (OpenEnumStr
                                  (["Low"; "Medium"; "High"; "Extreme"],
                                    "..."))),
                            "Control the verbosity of debugging info") ::
                            uu____40186
                           in
                        (FStar_Getopt.noshort, "debug",
                          (Accumulated (SimpleStr "module_name")),
                          "Print lots of debugging information while checking module")
                          :: uu____40172
                         in
                      (FStar_Getopt.noshort, "codegen-lib",
                        (Accumulated (SimpleStr "namespace")),
                        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                        :: uu____40158
                       in
                    (FStar_Getopt.noshort, "codegen",
                      (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                      "Generate code for further compilation to executable code, or build a compiler plugin")
                      :: uu____40144
                     in
                  uu____40110 :: uu____40130  in
                uu____40076 :: uu____40096  in
              (FStar_Getopt.noshort, "cache_dir",
                (PostProcessed (pp_validate_dir, (PathStr "dir"))),
                "Read and write .checked and .checked.lax in directory <dir>")
                :: uu____40062
               in
            uu____40028 :: uu____40048  in
          (FStar_Getopt.noshort, "already_cached",
            (Accumulated
               (SimpleStr
                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
            "\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")
            :: uu____40014
           in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____40000
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____39986
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___296_44251  ->
             match uu___296_44251 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____39972

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____44280  ->
    let uu____44283 = specs_with_types ()  in
    FStar_List.map
      (fun uu____44314  ->
         match uu____44314 with
         | (short,long,typ,doc) ->
             let uu____44336 =
               let uu____44350 = arg_spec_of_opt_type long typ  in
               (short, long, uu____44350, doc)  in
             mk_spec uu____44336) uu____44283

let (settable : Prims.string -> Prims.bool) =
  fun uu___297_44365  ->
    match uu___297_44365 with
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
    | uu____44488 -> false
  
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
       (fun uu____44587  ->
          match uu____44587 with
          | (uu____44602,x,uu____44604,uu____44605) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____44680  ->
          match uu____44680 with
          | (uu____44695,x,uu____44697,uu____44698) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____44714  ->
    let uu____44715 = specs ()  in display_usage_aux uu____44715
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____44747 -> true
    | uu____44750 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____44761 -> uu____44761
  
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
        (fun uu___759_44782  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____44799 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____44799
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____44835  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____44841 =
             let uu____44845 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____44845 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____44841)
       in
    let uu____44902 =
      let uu____44906 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____44906
       in
    (res, uu____44902)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____44948  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____44991 = specs ()  in
       FStar_Getopt.parse_cmdline uu____44991 (fun x  -> ())  in
     (let uu____44998 =
        let uu____45004 =
          let uu____45005 = FStar_List.map mk_string old_verify_module  in
          List uu____45005  in
        ("verify_module", uu____45004)  in
      set_option' uu____44998);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____45024 =
        let uu____45026 =
          let uu____45028 =
            let uu____45030 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____45030  in
          (FStar_String.length f1) - uu____45028  in
        uu____45026 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____45024  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____45043 = get_lax ()  in
    if uu____45043
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____45064 = module_name_of_file_name fn  in
    should_verify uu____45064
  
let (module_name_eq : Prims.string -> Prims.string -> Prims.bool) =
  fun m1  ->
    fun m2  -> (FStar_String.lowercase m1) = (FStar_String.lowercase m2)
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____45092 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____45092 (FStar_List.existsb (module_name_eq m))
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____45110 = should_verify m  in
    if uu____45110 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____45127  ->
    let cache_dir =
      let uu____45132 = get_cache_dir ()  in
      match uu____45132 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some c -> [c]  in
    let uu____45146 = get_no_default_includes ()  in
    if uu____45146
    then
      let uu____45152 = get_include ()  in
      FStar_List.append cache_dir uu____45152
    else
      (let lib_paths =
         let uu____45163 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____45163 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = FStar_String.op_Hat fstar_bin_directory "/.."
                in
             let defs = universe_include_path_base_dirs  in
             let uu____45179 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> FStar_String.op_Hat fstar_home x))
                in
             FStar_All.pipe_right uu____45179
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____45206 =
         let uu____45210 =
           let uu____45214 = get_include ()  in
           FStar_List.append uu____45214 ["."]  in
         FStar_List.append lib_paths uu____45210  in
       FStar_List.append cache_dir uu____45206)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____45241 = FStar_Util.smap_try_find file_map filename  in
    match uu____45241 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___810_45263  ->
               match () with
               | () ->
                   let uu____45267 = FStar_Util.is_path_absolute filename  in
                   if uu____45267
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____45283 =
                        let uu____45287 = include_path ()  in
                        FStar_List.rev uu____45287  in
                      FStar_Util.find_map uu____45283
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___809_45315 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____45335  ->
    let uu____45336 = get_prims ()  in
    match uu____45336 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____45345 = find_file filename  in
        (match uu____45345 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____45354 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____45354)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____45367  ->
    let uu____45368 = prims ()  in FStar_Util.basename uu____45368
  
let (pervasives : unit -> Prims.string) =
  fun uu____45376  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____45380 = find_file filename  in
    match uu____45380 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____45389 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____45389
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____45399  ->
    let uu____45400 = pervasives ()  in FStar_Util.basename uu____45400
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____45408  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____45412 = find_file filename  in
    match uu____45412 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____45421 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____45421
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____45434 = get_odir ()  in
    match uu____45434 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____45452 = get_cache_dir ()  in
    match uu____45452 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____45461 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____45461
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns  ->
    let cache = FStar_Util.smap_create (Prims.parse_int "31")  in
    let with_cache f s =
      let uu____45583 = FStar_Util.smap_try_find cache s  in
      match uu____45583 with
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
             let uu____45718 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____45718  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____45741 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              let s1 = FStar_Util.trim_string s  in
              if s1 = ""
              then []
              else
                with_cache
                  (fun s2  ->
                     let uu____45809 =
                       FStar_All.pipe_right (FStar_Util.splitlines s2)
                         (FStar_List.concatMap
                            (fun s3  -> FStar_Util.split s3 " "))
                        in
                     FStar_All.pipe_right uu____45809
                       (FStar_List.map parse_one_setting)) s1))
       in
    FStar_All.pipe_right uu____45741 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____45884 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____45884 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____45899  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____45908  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____45917  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____45924  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____45931  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____45938  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____45948 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____45959 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____45970 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____45981 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____45990  ->
    let uu____45991 = get_codegen ()  in
    FStar_Util.map_opt uu____45991
      (fun uu___298_45997  ->
         match uu___298_45997 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____46003 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____46016  ->
    let uu____46017 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____46017
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____46043  -> let uu____46044 = get_debug ()  in uu____46044 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____46061 = get_debug ()  in
    FStar_All.pipe_right uu____46061
      (FStar_List.existsb (module_name_eq modul))
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____46086 = get_debug ()  in
       FStar_All.pipe_right uu____46086
         (FStar_List.existsb (module_name_eq modul)))
        && (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____46101  ->
    let uu____46102 = get_defensive ()  in uu____46102 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____46112  ->
    let uu____46113 = get_defensive ()  in uu____46113 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46125  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____46132  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____46139  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____46146  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____46156 = get_dump_module ()  in
    FStar_All.pipe_right uu____46156 (FStar_List.existsb (module_name_eq s))
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____46171  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____46178  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____46188 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____46188
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____46224  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____46232  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____46239  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46248  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____46255  -> get_ide () 
let (print : unit -> Prims.bool) = fun uu____46262  -> get_print () 
let (print_in_place : unit -> Prims.bool) =
  fun uu____46269  -> get_print_in_place () 
let profile : 'a . (unit -> 'a) -> ('a -> Prims.string) -> 'a =
  fun f  ->
    fun msg  ->
      let uu____46300 = get_profile ()  in
      if uu____46300
      then
        let uu____46303 = FStar_Util.record_time f  in
        match uu____46303 with
        | (a,time) ->
            ((let uu____46314 = FStar_Util.string_of_int time  in
              let uu____46316 = msg a  in
              FStar_Util.print2 "Elapsed time %s ms: %s\n" uu____46314
                uu____46316);
             a)
      else f ()
  
let (protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____46327  -> get_protect_top_level_axioms () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____46334  ->
    let uu____46335 = get_initial_fuel ()  in
    let uu____46337 = get_max_fuel ()  in Prims.min uu____46335 uu____46337
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____46345  ->
    let uu____46346 = get_initial_ifuel ()  in
    let uu____46348 = get_max_ifuel ()  in Prims.min uu____46346 uu____46348
  
let (interactive : unit -> Prims.bool) =
  fun uu____46356  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____46363  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____46372  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____46379  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____46386  -> get_log_queries () 
let (keep_query_captions : unit -> Prims.bool) =
  fun uu____46393  -> (log_queries ()) && (get_keep_query_captions ()) 
let (log_types : unit -> Prims.bool) = fun uu____46400  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____46407  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____46414  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____46421  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____46428  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____46434  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____46443  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____46450  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____46460 = get_no_extract ()  in
    FStar_All.pipe_right uu____46460 (FStar_List.existsb (module_name_eq s))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____46475  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____46482  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____46489  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____46496  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46505  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____46512  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____46519  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____46526  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____46533  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____46540  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____46547  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____46554  -> get_print_z3_statistics () 
let (query_stats : unit -> Prims.bool) =
  fun uu____46561  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____46568  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46577  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____46584  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____46591  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____46598  ->
    let uu____46599 = get_smtencoding_nl_arith_repr ()  in
    uu____46599 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____46609  ->
    let uu____46610 = get_smtencoding_nl_arith_repr ()  in
    uu____46610 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____46620  ->
    let uu____46621 = get_smtencoding_nl_arith_repr ()  in
    uu____46621 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____46631  ->
    let uu____46632 = get_smtencoding_l_arith_repr ()  in
    uu____46632 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____46642  ->
    let uu____46643 = get_smtencoding_l_arith_repr ()  in
    uu____46643 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____46653  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____46660  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____46667  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____46674  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____46681  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____46688  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____46695  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____46702  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____46709  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____46716  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____46723  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____46730  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____46737  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____46744  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46753  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____46760  -> get_use_tactics () 
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu____46776  ->
    let uu____46777 = get_using_facts_from ()  in
    match uu____46777 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____46831  ->
    let uu____46832 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____46832
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____46843  ->
    let uu____46844 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____46844 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____46852 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____46863  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____46870  ->
    let uu____46871 = get_smt ()  in
    match uu____46871 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____46889  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____46896  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____46903  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____46910  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____46917  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____46924  ->
    (get_use_two_phase_tc ()) &&
      (let uu____46926 = lax ()  in Prims.op_Negation uu____46926)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____46934  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____46941  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____46948  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____46955  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____46962  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____46979 =
      let uu____46981 = trace_error ()  in Prims.op_Negation uu____46981  in
    if uu____46979
    then
      (push ();
       (let r =
          try
            (fun uu___1009_46996  ->
               match () with
               | () -> let uu____47001 = f ()  in FStar_Util.Inr uu____47001)
              ()
          with | uu___1008_47003 -> FStar_Util.Inl uu___1008_47003  in
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
        | (uu____47084,[]) -> true
        | (m2::ms,p::ps) ->
            (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
        | uu____47117 -> false  in
      let uu____47129 =
        FStar_All.pipe_right setting
          (FStar_Util.try_find
             (fun uu____47171  ->
                match uu____47171 with
                | (path,uu____47182) -> matches_path m_components path))
         in
      match uu____47129 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____47201,flag) -> flag
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____47230 = get_extract ()  in
    match uu____47230 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____47245 =
            let uu____47261 = get_no_extract ()  in
            let uu____47265 = get_extract_namespace ()  in
            let uu____47269 = get_extract_module ()  in
            (uu____47261, uu____47265, uu____47269)  in
          match uu____47245 with
          | ([],[],[]) -> ()
          | uu____47294 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         module_matches_namespace_filter m1 extract_setting)
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____47323 = get_extract_namespace ()  in
          match uu____47323 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____47351 = get_extract_module ()  in
          match uu____47351 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____47373 = no_extract m1  in Prims.op_Negation uu____47373)
          &&
          (let uu____47376 =
             let uu____47387 = get_extract_namespace ()  in
             let uu____47391 = get_extract_module ()  in
             (uu____47387, uu____47391)  in
           (match uu____47376 with
            | ([],[]) -> true
            | uu____47411 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  
let (should_be_already_cached : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____47431 = get_already_cached ()  in
    match uu____47431 with
    | FStar_Pervasives_Native.None  -> false
    | FStar_Pervasives_Native.Some already_cached_setting ->
        module_matches_namespace_filter m already_cached_setting
  
let (error_flags : unit -> error_flag Prims.list) =
  let cache = FStar_Util.smap_create (Prims.parse_int "10")  in
  fun uu____47464  ->
    let we = warn_error ()  in
    let uu____47467 = FStar_Util.smap_try_find cache we  in
    match uu____47467 with
    | FStar_Pervasives_Native.None  ->
        let r = parse_warn_error we  in (FStar_Util.smap_add cache we r; r)
    | FStar_Pervasives_Native.Some r -> r
  