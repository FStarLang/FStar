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
    match projectee with | Low  -> true | uu____34736 -> false
  
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____34747 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | High  -> true | uu____34758 -> false
  
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____34769 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____34782 -> false
  
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
    match projectee with | Bool _0 -> true | uu____34837 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____34861 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____34885 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____34909 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____34934 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____34959 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _34967  -> Bool _34967 
let (mk_string : Prims.string -> option_val) = fun _34974  -> String _34974 
let (mk_path : Prims.string -> option_val) = fun _34981  -> Path _34981 
let (mk_int : Prims.int -> option_val) = fun _34988  -> Int _34988 
let (mk_list : option_val Prims.list -> option_val) =
  fun _34996  -> List _34996 
type options =
  | Set 
  | Reset 
  | Restore 
let (uu___is_Set : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Set  -> true | uu____35006 -> false
  
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____35017 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____35028 -> false
  
type error_flag =
  | CFatal 
  | CAlwaysError 
  | CError 
  | CWarning 
  | CSilent 
let (uu___is_CFatal : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CFatal  -> true | uu____35039 -> false
  
let (uu___is_CAlwaysError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CAlwaysError  -> true | uu____35050 -> false
  
let (uu___is_CError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CError  -> true | uu____35061 -> false
  
let (uu___is_CWarning : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CWarning  -> true | uu____35072 -> false
  
let (uu___is_CSilent : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CSilent  -> true | uu____35083 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____35108  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____35135  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____35163  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___289_35192  ->
    match uu___289_35192 with
    | Bool b -> b
    | uu____35196 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___290_35205  ->
    match uu___290_35205 with
    | Int b -> b
    | uu____35209 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___291_35218  ->
    match uu___291_35218 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____35224 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___292_35234  ->
    match uu___292_35234 with
    | List ts -> ts
    | uu____35240 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____35251 .
    (option_val -> 'Auu____35251) -> option_val -> 'Auu____35251 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____35269 = as_list' x  in
      FStar_All.pipe_right uu____35269 (FStar_List.map as_t)
  
let as_option :
  'Auu____35283 .
    (option_val -> 'Auu____35283) ->
      option_val -> 'Auu____35283 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___293_35298  ->
      match uu___293_35298 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____35302 = as_t v1  in
          FStar_Pervasives_Native.Some uu____35302
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___294_35311  ->
    match uu___294_35311 with
    | List ls ->
        let uu____35318 =
          FStar_List.map
            (fun l  ->
               let uu____35330 = as_string l  in
               FStar_Util.split uu____35330 ",") ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____35318
    | uu____35342 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let copy_optionstate :
  'Auu____35354 .
    'Auu____35354 FStar_Util.smap -> 'Auu____35354 FStar_Util.smap
  = fun m  -> FStar_Util.smap_copy m 
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (internal_peek : unit -> optionstate) =
  fun uu____35395  ->
    let uu____35396 =
      let uu____35399 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____35399  in
    FStar_List.hd uu____35396
  
let (peek : unit -> optionstate) = fun uu____35438  -> internal_peek () 
let (pop : unit -> unit) =
  fun uu____35444  ->
    let uu____35445 = FStar_ST.op_Bang fstar_options  in
    match uu____35445 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____35480::[] -> failwith "TOO MANY POPS!"
    | uu____35488::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____35530  ->
    let uu____35531 =
      let uu____35536 =
        let uu____35539 =
          let uu____35542 = FStar_ST.op_Bang fstar_options  in
          FStar_List.hd uu____35542  in
        FStar_List.map copy_optionstate uu____35539  in
      let uu____35576 = FStar_ST.op_Bang fstar_options  in uu____35536 ::
        uu____35576
       in
    FStar_ST.op_Colon_Equals fstar_options uu____35531
  
let (internal_pop : unit -> Prims.bool) =
  fun uu____35643  ->
    let curstack =
      let uu____35647 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____35647  in
    match curstack with
    | [] -> failwith "impossible: empty current option stack"
    | uu____35684::[] -> false
    | uu____35686::tl1 ->
        ((let uu____35691 =
            let uu____35696 =
              let uu____35701 = FStar_ST.op_Bang fstar_options  in
              FStar_List.tl uu____35701  in
            tl1 :: uu____35696  in
          FStar_ST.op_Colon_Equals fstar_options uu____35691);
         true)
  
let (internal_push : unit -> unit) =
  fun uu____35770  ->
    let curstack =
      let uu____35774 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____35774  in
    let stack' =
      let uu____35811 =
        let uu____35812 = FStar_List.hd curstack  in
        copy_optionstate uu____35812  in
      uu____35811 :: curstack  in
    let uu____35815 =
      let uu____35820 =
        let uu____35825 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____35825  in
      stack' :: uu____35820  in
    FStar_ST.op_Colon_Equals fstar_options uu____35815
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____35894 = FStar_ST.op_Bang fstar_options  in
    match uu____35894 with
    | [] -> failwith "set on empty option stack"
    | []::uu____35929 -> failwith "set on empty current option stack"
    | (uu____35937::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
  
let (snapshot : unit -> (Prims.int * unit)) =
  fun uu____35987  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____36017 = peek ()  in FStar_Util.smap_add uu____36017 k v1
  
let (set_option' : (Prims.string * option_val) -> unit) =
  fun uu____36030  -> match uu____36030 with | (k,v1) -> set_option k v1 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____36069 =
      let uu____36073 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____36073
       in
    FStar_ST.op_Colon_Equals light_off_files uu____36069
  
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
    let uu____37043 = FStar_ST.op_Bang r  in
    match uu____37043 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some f)
    | uu____37178 -> failwith "Multiple initialization of FStar.Options"  in
  let get1 uu____37199 =
    let uu____37200 = FStar_ST.op_Bang r  in
    match uu____37200 with
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
    let uu____37361 = FStar_Pervasives_Native.snd parse_warn_error_set_get ()
       in
    uu____37361 s
  
let (init : unit -> unit) =
  fun uu____37392  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____37412  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____37485 =
      let uu____37488 = peek ()  in FStar_Util.smap_try_find uu____37488 s
       in
    match uu____37485 with
    | FStar_Pervasives_Native.None  ->
        let uu____37491 =
          let uu____37493 = FStar_String.op_Hat s " not found"  in
          FStar_String.op_Hat "Impossible: option " uu____37493  in
        failwith uu____37491
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____37505 .
    Prims.string -> (option_val -> 'Auu____37505) -> 'Auu____37505
  = fun s  -> fun c  -> let uu____37523 = get_option s  in c uu____37523 
let (get_abort_on : unit -> Prims.int) =
  fun uu____37530  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____37539  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____37550  -> lookup_opt "admit_except" (as_option as_string) 
let (get_already_cached :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____37566  ->
    lookup_opt "already_cached" (as_option (as_list as_string))
  
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____37583  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37594  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____37606  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____37615  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37626  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____37640  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____37654  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____37668  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____37679  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37690  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____37702  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____37711  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____37720  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____37731  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____37743  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____37752  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____37765  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____37784  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____37798  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____37810  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____37819  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____37828  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37839  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____37851  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____37860  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____37871  -> lookup_opt "include" (as_list as_string) 
let (get_print : unit -> Prims.bool) =
  fun uu____37883  -> lookup_opt "print" as_bool 
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____37892  -> lookup_opt "print_in_place" as_bool 
let (get_profile : unit -> Prims.bool) =
  fun uu____37901  -> lookup_opt "profile" as_bool 
let (get_protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____37910  -> lookup_opt "protect_top_level_axioms" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____37919  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____37928  -> lookup_opt "initial_ifuel" as_int 
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu____37937  -> lookup_opt "keep_query_captions" as_bool 
let (get_lax : unit -> Prims.bool) =
  fun uu____37946  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____37957  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____37969  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____37978  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____37987  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____37996  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____38005  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____38014  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____38023  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____38032  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____38043  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____38055  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____38064  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____38073  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____38082  ->
    lookup_opt "normalize_pure_terms_for_extraction" as_bool
  
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38093  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____38105  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38116  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____38128  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____38137  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____38146  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____38155  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____38164  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____38173  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____38182  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____38191  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____38200  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38211  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____38223  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38234  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____38246  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____38255  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____38264  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____38273  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____38282  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____38291  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____38300  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____38309  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____38318  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____38327  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____38336  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____38345  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____38354  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____38363  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____38372  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____38381  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____38390  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38401  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____38413  ->
    let uu____38414 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____38414
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____38428  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38447  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____38461  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____38475  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____38487  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____38496  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____38507  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____38519  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____38528  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____38537  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____38546  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____38555  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____38564  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____38573  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____38582  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____38591  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____38600  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___295_38609  ->
    match uu___295_38609 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____38630 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____38639 = get_debug_level ()  in
    FStar_All.pipe_right uu____38639
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "<not set>" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____38805  ->
    let uu____38806 =
      let uu____38808 = FStar_ST.op_Bang _version  in
      let uu____38831 = FStar_ST.op_Bang _platform  in
      let uu____38854 = FStar_ST.op_Bang _compiler  in
      let uu____38877 = FStar_ST.op_Bang _date  in
      let uu____38900 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____38808
        uu____38831 uu____38854 uu____38877 uu____38900
       in
    FStar_Util.print_string uu____38806
  
let display_usage_aux :
  'Auu____38931 'Auu____38932 .
    ('Auu____38931 * Prims.string * 'Auu____38932 FStar_Getopt.opt_variant *
      Prims.string) Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____38987  ->
         match uu____38987 with
         | (uu____39000,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____39019 =
                      let uu____39021 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____39021  in
                    FStar_Util.print_string uu____39019
                  else
                    (let uu____39026 =
                       let uu____39028 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____39028 doc  in
                     FStar_Util.print_string uu____39026)
              | FStar_Getopt.OneArg (uu____39031,argname) ->
                  if doc = ""
                  then
                    let uu____39046 =
                      let uu____39048 = FStar_Util.colorize_bold flag  in
                      let uu____39050 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____39048
                        uu____39050
                       in
                    FStar_Util.print_string uu____39046
                  else
                    (let uu____39055 =
                       let uu____39057 = FStar_Util.colorize_bold flag  in
                       let uu____39059 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____39057
                         uu____39059 doc
                        in
                     FStar_Util.print_string uu____39055))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____39094 = o  in
    match uu____39094 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____39136 =
                let uu____39137 = f ()  in set_option name uu____39137  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____39158 = f x  in set_option name uu____39158
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____39185 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____39185  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____39211 =
        let uu____39214 = lookup_opt name as_list'  in
        FStar_List.append uu____39214 [value]  in
      mk_list uu____39211
  
let accumulate_string :
  'Auu____39228 .
    Prims.string -> ('Auu____39228 -> Prims.string) -> 'Auu____39228 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____39253 =
          let uu____39254 =
            let uu____39255 = post_processor value  in mk_string uu____39255
             in
          accumulated_option name uu____39254  in
        set_option name uu____39253
  
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
    match projectee with | Const _0 -> true | uu____39377 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____39398 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____39420 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____39433 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____39457 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____39483 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____39520 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____39571 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____39612 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____39632 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____39659 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____39703 -> true
    | uu____39706 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____39717 -> uu____39717
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___581_39741  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____39743 ->
                      let uu____39745 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____39745 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____39753 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____39753
                  | PathStr uu____39770 -> mk_path str_val
                  | SimpleStr uu____39772 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____39782 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____39799 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____39799
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
            let uu____39819 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____39819
  
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ  ->
    let desc_of_enum cases =
      let uu____39849 =
        let uu____39851 =
          FStar_String.op_Hat (FStar_String.concat "|" cases) "]"  in
        FStar_String.op_Hat "[" uu____39851  in
      FStar_Pervasives_Native.Some uu____39849  in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____39893,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____39903,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____39934 = desc_of_opt_type typ  in
      match uu____39934 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____39942  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____39968 =
      let uu____39970 = as_string s  in FStar_String.lowercase uu____39970
       in
    mk_string uu____39968
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string)
      Prims.list)
  =
  fun uu____40027  ->
    let uu____40041 =
      let uu____40055 =
        let uu____40069 =
          let uu____40083 =
            let uu____40097 =
              let uu____40109 =
                let uu____40110 = mk_bool true  in Const uu____40110  in
              (FStar_Getopt.noshort, "cache_checked_modules", uu____40109,
                "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
               in
            let uu____40117 =
              let uu____40131 =
                let uu____40145 =
                  let uu____40157 =
                    let uu____40158 = mk_bool true  in Const uu____40158  in
                  (FStar_Getopt.noshort, "cache_off", uu____40157,
                    "Do not read or write any .checked files")
                   in
                let uu____40165 =
                  let uu____40179 =
                    let uu____40191 =
                      let uu____40192 = mk_bool true  in Const uu____40192
                       in
                    (FStar_Getopt.noshort, "cmi", uu____40191,
                      "Inline across module interfaces during extraction (aka. cross-module inlining)")
                     in
                  let uu____40199 =
                    let uu____40213 =
                      let uu____40227 =
                        let uu____40241 =
                          let uu____40255 =
                            let uu____40269 =
                              let uu____40283 =
                                let uu____40297 =
                                  let uu____40309 =
                                    let uu____40310 = mk_bool true  in
                                    Const uu____40310  in
                                  (FStar_Getopt.noshort, "detail_errors",
                                    uu____40309,
                                    "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                   in
                                let uu____40317 =
                                  let uu____40331 =
                                    let uu____40343 =
                                      let uu____40344 = mk_bool true  in
                                      Const uu____40344  in
                                    (FStar_Getopt.noshort,
                                      "detail_hint_replay", uu____40343,
                                      "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                     in
                                  let uu____40351 =
                                    let uu____40365 =
                                      let uu____40377 =
                                        let uu____40378 = mk_bool true  in
                                        Const uu____40378  in
                                      (FStar_Getopt.noshort, "doc",
                                        uu____40377,
                                        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                       in
                                    let uu____40385 =
                                      let uu____40399 =
                                        let uu____40413 =
                                          let uu____40425 =
                                            let uu____40426 = mk_bool true
                                               in
                                            Const uu____40426  in
                                          (FStar_Getopt.noshort,
                                            "eager_inference", uu____40425,
                                            "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                           in
                                        let uu____40433 =
                                          let uu____40447 =
                                            let uu____40459 =
                                              let uu____40460 = mk_bool true
                                                 in
                                              Const uu____40460  in
                                            (FStar_Getopt.noshort,
                                              "eager_subtyping", uu____40459,
                                              "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                             in
                                          let uu____40467 =
                                            let uu____40481 =
                                              let uu____40495 =
                                                let uu____40509 =
                                                  let uu____40523 =
                                                    let uu____40535 =
                                                      let uu____40536 =
                                                        mk_bool true  in
                                                      Const uu____40536  in
                                                    (FStar_Getopt.noshort,
                                                      "expose_interfaces",
                                                      uu____40535,
                                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                     in
                                                  let uu____40543 =
                                                    let uu____40557 =
                                                      let uu____40569 =
                                                        let uu____40570 =
                                                          mk_bool true  in
                                                        Const uu____40570  in
                                                      (FStar_Getopt.noshort,
                                                        "hide_uvar_nums",
                                                        uu____40569,
                                                        "Don't print unification variable numbers")
                                                       in
                                                    let uu____40577 =
                                                      let uu____40591 =
                                                        let uu____40605 =
                                                          let uu____40617 =
                                                            let uu____40618 =
                                                              mk_bool true
                                                               in
                                                            Const uu____40618
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "hint_info",
                                                            uu____40617,
                                                            "Print information regarding hints (deprecated; use --query_stats instead)")
                                                           in
                                                        let uu____40625 =
                                                          let uu____40639 =
                                                            let uu____40651 =
                                                              let uu____40652
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____40652
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "in",
                                                              uu____40651,
                                                              "Legacy interactive mode; reads input from stdin")
                                                             in
                                                          let uu____40659 =
                                                            let uu____40673 =
                                                              let uu____40685
                                                                =
                                                                let uu____40686
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____40686
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "ide",
                                                                uu____40685,
                                                                "JSON-based interactive mode for IDEs")
                                                               in
                                                            let uu____40693 =
                                                              let uu____40707
                                                                =
                                                                let uu____40721
                                                                  =
                                                                  let uu____40733
                                                                    =
                                                                    let uu____40734
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40734
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "print",
                                                                    uu____40733,
                                                                    "Parses and prettyprints the files included on the command line")
                                                                   in
                                                                let uu____40741
                                                                  =
                                                                  let uu____40755
                                                                    =
                                                                    let uu____40767
                                                                    =
                                                                    let uu____40768
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40768
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_in_place",
                                                                    uu____40767,
                                                                    "Parses and prettyprints in place the files included on the command line")
                                                                     in
                                                                  let uu____40775
                                                                    =
                                                                    let uu____40789
                                                                    =
                                                                    let uu____40801
                                                                    =
                                                                    let uu____40802
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40802
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "profile",
                                                                    uu____40801,
                                                                    "Prints timing information for various operations in the compiler")
                                                                     in
                                                                    let uu____40809
                                                                    =
                                                                    let uu____40823
                                                                    =
                                                                    let uu____40837
                                                                    =
                                                                    let uu____40851
                                                                    =
                                                                    let uu____40865
                                                                    =
                                                                    let uu____40879
                                                                    =
                                                                    let uu____40891
                                                                    =
                                                                    let uu____40892
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40892
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____40891,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____40899
                                                                    =
                                                                    let uu____40913
                                                                    =
                                                                    let uu____40927
                                                                    =
                                                                    let uu____40939
                                                                    =
                                                                    let uu____40940
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40940
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____40939,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____40947
                                                                    =
                                                                    let uu____40961
                                                                    =
                                                                    let uu____40973
                                                                    =
                                                                    let uu____40974
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40974
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____40973,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____40981
                                                                    =
                                                                    let uu____40995
                                                                    =
                                                                    let uu____41009
                                                                    =
                                                                    let uu____41023
                                                                    =
                                                                    let uu____41037
                                                                    =
                                                                    let uu____41049
                                                                    =
                                                                    let uu____41050
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41050
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____41049,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____41057
                                                                    =
                                                                    let uu____41071
                                                                    =
                                                                    let uu____41085
                                                                    =
                                                                    let uu____41097
                                                                    =
                                                                    let uu____41098
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41098
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____41097,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____41105
                                                                    =
                                                                    let uu____41119
                                                                    =
                                                                    let uu____41133
                                                                    =
                                                                    let uu____41145
                                                                    =
                                                                    let uu____41146
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41146
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____41145,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____41153
                                                                    =
                                                                    let uu____41167
                                                                    =
                                                                    let uu____41179
                                                                    =
                                                                    let uu____41180
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41180
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____41179,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____41187
                                                                    =
                                                                    let uu____41201
                                                                    =
                                                                    let uu____41213
                                                                    =
                                                                    let uu____41214
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41214
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____41213,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____41221
                                                                    =
                                                                    let uu____41235
                                                                    =
                                                                    let uu____41249
                                                                    =
                                                                    let uu____41263
                                                                    =
                                                                    let uu____41275
                                                                    =
                                                                    let uu____41276
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41276
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____41275,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____41283
                                                                    =
                                                                    let uu____41297
                                                                    =
                                                                    let uu____41309
                                                                    =
                                                                    let uu____41310
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41310
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____41309,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____41317
                                                                    =
                                                                    let uu____41331
                                                                    =
                                                                    let uu____41343
                                                                    =
                                                                    let uu____41344
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41344
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____41343,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____41351
                                                                    =
                                                                    let uu____41365
                                                                    =
                                                                    let uu____41377
                                                                    =
                                                                    let uu____41378
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41378
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____41377,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____41385
                                                                    =
                                                                    let uu____41399
                                                                    =
                                                                    let uu____41411
                                                                    =
                                                                    let uu____41412
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41412
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____41411,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____41419
                                                                    =
                                                                    let uu____41433
                                                                    =
                                                                    let uu____41445
                                                                    =
                                                                    let uu____41446
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41446
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____41445,
                                                                    "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)")
                                                                     in
                                                                    let uu____41453
                                                                    =
                                                                    let uu____41467
                                                                    =
                                                                    let uu____41479
                                                                    =
                                                                    let uu____41480
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41480
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____41479,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____41487
                                                                    =
                                                                    let uu____41501
                                                                    =
                                                                    let uu____41513
                                                                    =
                                                                    let uu____41514
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41514
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____41513,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____41521
                                                                    =
                                                                    let uu____41535
                                                                    =
                                                                    let uu____41547
                                                                    =
                                                                    let uu____41548
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41548
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____41547,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____41555
                                                                    =
                                                                    let uu____41569
                                                                    =
                                                                    let uu____41583
                                                                    =
                                                                    let uu____41595
                                                                    =
                                                                    let uu____41596
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41596
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____41595,
                                                                    "Disable all non-critical output")
                                                                     in
                                                                    let uu____41603
                                                                    =
                                                                    let uu____41617
                                                                    =
                                                                    let uu____41631
                                                                    =
                                                                    let uu____41645
                                                                    =
                                                                    let uu____41659
                                                                    =
                                                                    let uu____41673
                                                                    =
                                                                    let uu____41685
                                                                    =
                                                                    let uu____41686
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41686
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____41685,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____41693
                                                                    =
                                                                    let uu____41707
                                                                    =
                                                                    let uu____41719
                                                                    =
                                                                    let uu____41720
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41720
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____41719,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____41727
                                                                    =
                                                                    let uu____41741
                                                                    =
                                                                    let uu____41753
                                                                    =
                                                                    let uu____41754
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41754
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____41753,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____41761
                                                                    =
                                                                    let uu____41775
                                                                    =
                                                                    let uu____41787
                                                                    =
                                                                    let uu____41788
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41788
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____41787,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____41795
                                                                    =
                                                                    let uu____41809
                                                                    =
                                                                    let uu____41823
                                                                    =
                                                                    let uu____41835
                                                                    =
                                                                    let uu____41836
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41836
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____41835,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____41843
                                                                    =
                                                                    let uu____41857
                                                                    =
                                                                    let uu____41871
                                                                    =
                                                                    let uu____41883
                                                                    =
                                                                    let uu____41884
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41884
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____41883,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____41891
                                                                    =
                                                                    let uu____41905
                                                                    =
                                                                    let uu____41917
                                                                    =
                                                                    let uu____41918
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41918
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____41917,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____41925
                                                                    =
                                                                    let uu____41939
                                                                    =
                                                                    let uu____41951
                                                                    =
                                                                    let uu____41952
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41952
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____41951,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____41959
                                                                    =
                                                                    let uu____41973
                                                                    =
                                                                    let uu____41985
                                                                    =
                                                                    let uu____41986
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41986
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____41985,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____41993
                                                                    =
                                                                    let uu____42007
                                                                    =
                                                                    let uu____42019
                                                                    =
                                                                    let uu____42020
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42020
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____42019,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____42027
                                                                    =
                                                                    let uu____42041
                                                                    =
                                                                    let uu____42053
                                                                    =
                                                                    let uu____42054
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42054
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____42053,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____42061
                                                                    =
                                                                    let uu____42075
                                                                    =
                                                                    let uu____42087
                                                                    =
                                                                    let uu____42088
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42088
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____42087,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____42095
                                                                    =
                                                                    let uu____42109
                                                                    =
                                                                    let uu____42121
                                                                    =
                                                                    let uu____42122
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42122
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____42121,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____42129
                                                                    =
                                                                    let uu____42143
                                                                    =
                                                                    let uu____42157
                                                                    =
                                                                    let uu____42169
                                                                    =
                                                                    let uu____42170
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42170
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____42169,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____42177
                                                                    =
                                                                    let uu____42191
                                                                    =
                                                                    let uu____42203
                                                                    =
                                                                    let uu____42204
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42204
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____42203,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____42211
                                                                    =
                                                                    let uu____42225
                                                                    =
                                                                    let uu____42239
                                                                    =
                                                                    let uu____42253
                                                                    =
                                                                    let uu____42267
                                                                    =
                                                                    let uu____42279
                                                                    =
                                                                    let uu____42280
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42280
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____42279,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____42287
                                                                    =
                                                                    let uu____42301
                                                                    =
                                                                    let uu____42313
                                                                    =
                                                                    let uu____42314
                                                                    =
                                                                    let uu____42322
                                                                    =
                                                                    let uu____42323
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42323
                                                                     in
                                                                    ((fun
                                                                    uu____42330
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____42322)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42314
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____42313,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____42339
                                                                    =
                                                                    let uu____42353
                                                                    =
                                                                    let uu____42365
                                                                    =
                                                                    let uu____42366
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42366
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____42365,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____42373
                                                                    =
                                                                    let uu____42387
                                                                    =
                                                                    let uu____42401
                                                                    =
                                                                    let uu____42413
                                                                    =
                                                                    let uu____42414
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42414
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____42413,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____42421
                                                                    =
                                                                    let uu____42435
                                                                    =
                                                                    let uu____42449
                                                                    =
                                                                    let uu____42463
                                                                    =
                                                                    let uu____42477
                                                                    =
                                                                    let uu____42491
                                                                    =
                                                                    let uu____42503
                                                                    =
                                                                    let uu____42504
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42504
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____42503,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____42511
                                                                    =
                                                                    let uu____42525
                                                                    =
                                                                    let uu____42537
                                                                    =
                                                                    let uu____42538
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42538
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____42537,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____42545
                                                                    =
                                                                    let uu____42559
                                                                    =
                                                                    let uu____42573
                                                                    =
                                                                    let uu____42587
                                                                    =
                                                                    let uu____42601
                                                                    =
                                                                    let uu____42613
                                                                    =
                                                                    let uu____42614
                                                                    =
                                                                    let uu____42622
                                                                    =
                                                                    let uu____42623
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42623
                                                                     in
                                                                    ((fun
                                                                    uu____42629
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____42622)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42614
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____42613,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____42657
                                                                    =
                                                                    let uu____42671
                                                                    =
                                                                    let uu____42683
                                                                    =
                                                                    let uu____42684
                                                                    =
                                                                    let uu____42692
                                                                    =
                                                                    let uu____42693
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42693
                                                                     in
                                                                    ((fun
                                                                    uu____42699
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____42692)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42684
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____42683,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____42727
                                                                    =
                                                                    let uu____42741
                                                                    =
                                                                    let uu____42753
                                                                    =
                                                                    let uu____42754
                                                                    =
                                                                    let uu____42762
                                                                    =
                                                                    let uu____42763
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42763
                                                                     in
                                                                    ((fun
                                                                    uu____42770
                                                                     ->
                                                                    (
                                                                    let uu____42772
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____42772);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____42762)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42754
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____42753,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____42741]
                                                                     in
                                                                    uu____42671
                                                                    ::
                                                                    uu____42727
                                                                     in
                                                                    uu____42601
                                                                    ::
                                                                    uu____42657
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____42587
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____42573
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____42559
                                                                     in
                                                                    uu____42525
                                                                    ::
                                                                    uu____42545
                                                                     in
                                                                    uu____42491
                                                                    ::
                                                                    uu____42511
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____42477
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____42463
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____42449
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____42435
                                                                     in
                                                                    uu____42401
                                                                    ::
                                                                    uu____42421
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____42387
                                                                     in
                                                                    uu____42353
                                                                    ::
                                                                    uu____42373
                                                                     in
                                                                    uu____42301
                                                                    ::
                                                                    uu____42339
                                                                     in
                                                                    uu____42267
                                                                    ::
                                                                    uu____42287
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____42253
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____42239
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____42225
                                                                     in
                                                                    uu____42191
                                                                    ::
                                                                    uu____42211
                                                                     in
                                                                    uu____42157
                                                                    ::
                                                                    uu____42177
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____42143
                                                                     in
                                                                    uu____42109
                                                                    ::
                                                                    uu____42129
                                                                     in
                                                                    uu____42075
                                                                    ::
                                                                    uu____42095
                                                                     in
                                                                    uu____42041
                                                                    ::
                                                                    uu____42061
                                                                     in
                                                                    uu____42007
                                                                    ::
                                                                    uu____42027
                                                                     in
                                                                    uu____41973
                                                                    ::
                                                                    uu____41993
                                                                     in
                                                                    uu____41939
                                                                    ::
                                                                    uu____41959
                                                                     in
                                                                    uu____41905
                                                                    ::
                                                                    uu____41925
                                                                     in
                                                                    uu____41871
                                                                    ::
                                                                    uu____41891
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____41857
                                                                     in
                                                                    uu____41823
                                                                    ::
                                                                    uu____41843
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____41809
                                                                     in
                                                                    uu____41775
                                                                    ::
                                                                    uu____41795
                                                                     in
                                                                    uu____41741
                                                                    ::
                                                                    uu____41761
                                                                     in
                                                                    uu____41707
                                                                    ::
                                                                    uu____41727
                                                                     in
                                                                    uu____41673
                                                                    ::
                                                                    uu____41693
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____41659
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____41645
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____41631
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____41617
                                                                     in
                                                                    uu____41583
                                                                    ::
                                                                    uu____41603
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____41569
                                                                     in
                                                                    uu____41535
                                                                    ::
                                                                    uu____41555
                                                                     in
                                                                    uu____41501
                                                                    ::
                                                                    uu____41521
                                                                     in
                                                                    uu____41467
                                                                    ::
                                                                    uu____41487
                                                                     in
                                                                    uu____41433
                                                                    ::
                                                                    uu____41453
                                                                     in
                                                                    uu____41399
                                                                    ::
                                                                    uu____41419
                                                                     in
                                                                    uu____41365
                                                                    ::
                                                                    uu____41385
                                                                     in
                                                                    uu____41331
                                                                    ::
                                                                    uu____41351
                                                                     in
                                                                    uu____41297
                                                                    ::
                                                                    uu____41317
                                                                     in
                                                                    uu____41263
                                                                    ::
                                                                    uu____41283
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____41249
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____41235
                                                                     in
                                                                    uu____41201
                                                                    ::
                                                                    uu____41221
                                                                     in
                                                                    uu____41167
                                                                    ::
                                                                    uu____41187
                                                                     in
                                                                    uu____41133
                                                                    ::
                                                                    uu____41153
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____41119
                                                                     in
                                                                    uu____41085
                                                                    ::
                                                                    uu____41105
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____41071
                                                                     in
                                                                    uu____41037
                                                                    ::
                                                                    uu____41057
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____41023
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____41009
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____40995
                                                                     in
                                                                    uu____40961
                                                                    ::
                                                                    uu____40981
                                                                     in
                                                                    uu____40927
                                                                    ::
                                                                    uu____40947
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____40913
                                                                     in
                                                                    uu____40879
                                                                    ::
                                                                    uu____40899
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    "Retain comments in the logged SMT queries (requires --log_queries; default true)")
                                                                    ::
                                                                    uu____40865
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____40851
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try initially (default 2)")
                                                                    ::
                                                                    uu____40837
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "protect_top_level_axioms",
                                                                    BoolStr,
                                                                    "Guard nullary top-level symbols in the SMT encoding from provide ambient ground facts (default 'true')")
                                                                    ::
                                                                    uu____40823
                                                                     in
                                                                    uu____40789
                                                                    ::
                                                                    uu____40809
                                                                     in
                                                                  uu____40755
                                                                    ::
                                                                    uu____40775
                                                                   in
                                                                uu____40721
                                                                  ::
                                                                  uu____40741
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "include",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "path")),
                                                                "A directory in which to search for files included on the command line")
                                                                ::
                                                                uu____40707
                                                               in
                                                            uu____40673 ::
                                                              uu____40693
                                                             in
                                                          uu____40639 ::
                                                            uu____40659
                                                           in
                                                        uu____40605 ::
                                                          uu____40625
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "hint_file",
                                                        (PathStr "path"),
                                                        "Read/write hints to <path> (instead of module-specific hints files)")
                                                        :: uu____40591
                                                       in
                                                    uu____40557 ::
                                                      uu____40577
                                                     in
                                                  uu____40523 :: uu____40543
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "extract_namespace",
                                                  (Accumulated
                                                     (PostProcessed
                                                        (pp_lowercase,
                                                          (SimpleStr
                                                             "namespace name")))),
                                                  "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                  :: uu____40509
                                                 in
                                              (FStar_Getopt.noshort,
                                                "extract_module",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "module_name")))),
                                                "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                                :: uu____40495
                                               in
                                            (FStar_Getopt.noshort, "extract",
                                              (Accumulated
                                                 (SimpleStr
                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                              "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                              :: uu____40481
                                             in
                                          uu____40447 :: uu____40467  in
                                        uu____40413 :: uu____40433  in
                                      (FStar_Getopt.noshort, "dump_module",
                                        (Accumulated
                                           (SimpleStr "module_name")), "")
                                        :: uu____40399
                                       in
                                    uu____40365 :: uu____40385  in
                                  uu____40331 :: uu____40351  in
                                uu____40297 :: uu____40317  in
                              (FStar_Getopt.noshort, "dep",
                                (EnumStr ["make"; "graph"; "full"; "raw"]),
                                "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                                :: uu____40283
                               in
                            (FStar_Getopt.noshort, "defensive",
                              (EnumStr ["no"; "warn"; "fail"]),
                              "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                              :: uu____40269
                             in
                          (FStar_Getopt.noshort, "debug_level",
                            (Accumulated
                               (OpenEnumStr
                                  (["Low"; "Medium"; "High"; "Extreme"],
                                    "..."))),
                            "Control the verbosity of debugging info") ::
                            uu____40255
                           in
                        (FStar_Getopt.noshort, "debug",
                          (Accumulated (SimpleStr "module_name")),
                          "Print lots of debugging information while checking module")
                          :: uu____40241
                         in
                      (FStar_Getopt.noshort, "codegen-lib",
                        (Accumulated (SimpleStr "namespace")),
                        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                        :: uu____40227
                       in
                    (FStar_Getopt.noshort, "codegen",
                      (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                      "Generate code for further compilation to executable code, or build a compiler plugin")
                      :: uu____40213
                     in
                  uu____40179 :: uu____40199  in
                uu____40145 :: uu____40165  in
              (FStar_Getopt.noshort, "cache_dir",
                (PostProcessed (pp_validate_dir, (PathStr "dir"))),
                "Read and write .checked and .checked.lax in directory <dir>")
                :: uu____40131
               in
            uu____40097 :: uu____40117  in
          (FStar_Getopt.noshort, "already_cached",
            (Accumulated
               (SimpleStr
                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
            "\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")
            :: uu____40083
           in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____40069
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____40055
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___296_44320  ->
             match uu___296_44320 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____40041

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____44349  ->
    let uu____44352 = specs_with_types ()  in
    FStar_List.map
      (fun uu____44383  ->
         match uu____44383 with
         | (short,long,typ,doc) ->
             let uu____44405 =
               let uu____44419 = arg_spec_of_opt_type long typ  in
               (short, long, uu____44419, doc)  in
             mk_spec uu____44405) uu____44352

let (settable : Prims.string -> Prims.bool) =
  fun uu___297_44434  ->
    match uu___297_44434 with
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
    | uu____44557 -> false
  
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
       (fun uu____44656  ->
          match uu____44656 with
          | (uu____44671,x,uu____44673,uu____44674) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____44749  ->
          match uu____44749 with
          | (uu____44764,x,uu____44766,uu____44767) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____44783  ->
    let uu____44784 = specs ()  in display_usage_aux uu____44784
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____44816 -> true
    | uu____44819 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____44830 -> uu____44830
  
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
        (fun uu___759_44851  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____44868 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____44868
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____44904  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____44910 =
             let uu____44914 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____44914 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____44910)
       in
    let uu____44971 =
      let uu____44975 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____44975
       in
    (res, uu____44971)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____45017  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____45060 = specs ()  in
       FStar_Getopt.parse_cmdline uu____45060 (fun x  -> ())  in
     (let uu____45067 =
        let uu____45073 =
          let uu____45074 = FStar_List.map mk_string old_verify_module  in
          List uu____45074  in
        ("verify_module", uu____45073)  in
      set_option' uu____45067);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____45093 =
        let uu____45095 =
          let uu____45097 =
            let uu____45099 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____45099  in
          (FStar_String.length f1) - uu____45097  in
        uu____45095 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____45093  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____45112 = get_lax ()  in
    if uu____45112
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____45133 = module_name_of_file_name fn  in
    should_verify uu____45133
  
let (module_name_eq : Prims.string -> Prims.string -> Prims.bool) =
  fun m1  ->
    fun m2  -> (FStar_String.lowercase m1) = (FStar_String.lowercase m2)
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____45161 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____45161 (FStar_List.existsb (module_name_eq m))
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____45179 = should_verify m  in
    if uu____45179 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____45196  ->
    let cache_dir =
      let uu____45201 = get_cache_dir ()  in
      match uu____45201 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some c -> [c]  in
    let uu____45215 = get_no_default_includes ()  in
    if uu____45215
    then
      let uu____45221 = get_include ()  in
      FStar_List.append cache_dir uu____45221
    else
      (let lib_paths =
         let uu____45232 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____45232 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = FStar_String.op_Hat fstar_bin_directory "/.."
                in
             let defs = universe_include_path_base_dirs  in
             let uu____45248 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> FStar_String.op_Hat fstar_home x))
                in
             FStar_All.pipe_right uu____45248
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____45275 =
         let uu____45279 =
           let uu____45283 = get_include ()  in
           FStar_List.append uu____45283 ["."]  in
         FStar_List.append lib_paths uu____45279  in
       FStar_List.append cache_dir uu____45275)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____45310 = FStar_Util.smap_try_find file_map filename  in
    match uu____45310 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___810_45332  ->
               match () with
               | () ->
                   let uu____45336 = FStar_Util.is_path_absolute filename  in
                   if uu____45336
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____45352 =
                        let uu____45356 = include_path ()  in
                        FStar_List.rev uu____45356  in
                      FStar_Util.find_map uu____45352
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___809_45384 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____45404  ->
    let uu____45405 = get_prims ()  in
    match uu____45405 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____45414 = find_file filename  in
        (match uu____45414 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____45423 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____45423)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____45436  ->
    let uu____45437 = prims ()  in FStar_Util.basename uu____45437
  
let (pervasives : unit -> Prims.string) =
  fun uu____45445  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____45449 = find_file filename  in
    match uu____45449 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____45458 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____45458
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____45468  ->
    let uu____45469 = pervasives ()  in FStar_Util.basename uu____45469
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____45477  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____45481 = find_file filename  in
    match uu____45481 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____45490 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____45490
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____45503 = get_odir ()  in
    match uu____45503 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____45521 = get_cache_dir ()  in
    match uu____45521 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____45530 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____45530
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns  ->
    let cache = FStar_Util.smap_create (Prims.parse_int "31")  in
    let with_cache f s =
      let uu____45652 = FStar_Util.smap_try_find cache s  in
      match uu____45652 with
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
             let uu____45787 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____45787  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____45810 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              let s1 = FStar_Util.trim_string s  in
              if s1 = ""
              then []
              else
                with_cache
                  (fun s2  ->
                     let uu____45878 =
                       FStar_All.pipe_right (FStar_Util.splitlines s2)
                         (FStar_List.concatMap
                            (fun s3  -> FStar_Util.split s3 " "))
                        in
                     FStar_All.pipe_right uu____45878
                       (FStar_List.map parse_one_setting)) s1))
       in
    FStar_All.pipe_right uu____45810 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____45953 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____45953 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____45968  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____45977  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____45986  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____45993  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____46000  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____46007  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____46017 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____46028 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____46039 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____46050 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____46059  ->
    let uu____46060 = get_codegen ()  in
    FStar_Util.map_opt uu____46060
      (fun uu___298_46066  ->
         match uu___298_46066 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____46072 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____46085  ->
    let uu____46086 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____46086
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____46112  -> let uu____46113 = get_debug ()  in uu____46113 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____46130 = get_debug ()  in
    FStar_All.pipe_right uu____46130
      (FStar_List.existsb (module_name_eq modul))
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____46155 = get_debug ()  in
       FStar_All.pipe_right uu____46155
         (FStar_List.existsb (module_name_eq modul)))
        && (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____46170  ->
    let uu____46171 = get_defensive ()  in uu____46171 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____46181  ->
    let uu____46182 = get_defensive ()  in uu____46182 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46194  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____46201  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____46208  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____46215  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____46225 = get_dump_module ()  in
    FStar_All.pipe_right uu____46225 (FStar_List.existsb (module_name_eq s))
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____46240  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____46247  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____46257 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____46257
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____46293  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____46301  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____46308  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46317  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____46324  -> get_ide () 
let (print : unit -> Prims.bool) = fun uu____46331  -> get_print () 
let (print_in_place : unit -> Prims.bool) =
  fun uu____46338  -> get_print_in_place () 
let profile : 'a . (unit -> 'a) -> ('a -> Prims.string) -> 'a =
  fun f  ->
    fun msg  ->
      let uu____46369 = get_profile ()  in
      if uu____46369
      then
        let uu____46372 = FStar_Util.record_time f  in
        match uu____46372 with
        | (a,time) ->
            ((let uu____46383 = FStar_Util.string_of_int time  in
              let uu____46385 = msg a  in
              FStar_Util.print2 "Elapsed time %s ms: %s\n" uu____46383
                uu____46385);
             a)
      else f ()
  
let (protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____46396  -> get_protect_top_level_axioms () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____46403  ->
    let uu____46404 = get_initial_fuel ()  in
    let uu____46406 = get_max_fuel ()  in Prims.min uu____46404 uu____46406
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____46414  ->
    let uu____46415 = get_initial_ifuel ()  in
    let uu____46417 = get_max_ifuel ()  in Prims.min uu____46415 uu____46417
  
let (interactive : unit -> Prims.bool) =
  fun uu____46425  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____46432  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____46441  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____46448  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____46455  -> get_log_queries () 
let (keep_query_captions : unit -> Prims.bool) =
  fun uu____46462  -> (log_queries ()) && (get_keep_query_captions ()) 
let (log_types : unit -> Prims.bool) = fun uu____46469  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____46476  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____46483  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____46490  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____46497  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____46503  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____46512  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____46519  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____46529 = get_no_extract ()  in
    FStar_All.pipe_right uu____46529 (FStar_List.existsb (module_name_eq s))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____46544  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____46551  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____46558  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____46565  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46574  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____46581  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____46588  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____46595  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____46602  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____46609  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____46616  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____46623  -> get_print_z3_statistics () 
let (query_stats : unit -> Prims.bool) =
  fun uu____46630  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____46637  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46646  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____46653  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____46660  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____46667  ->
    let uu____46668 = get_smtencoding_nl_arith_repr ()  in
    uu____46668 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____46678  ->
    let uu____46679 = get_smtencoding_nl_arith_repr ()  in
    uu____46679 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____46689  ->
    let uu____46690 = get_smtencoding_nl_arith_repr ()  in
    uu____46690 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____46700  ->
    let uu____46701 = get_smtencoding_l_arith_repr ()  in
    uu____46701 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____46711  ->
    let uu____46712 = get_smtencoding_l_arith_repr ()  in
    uu____46712 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____46722  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____46729  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____46736  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____46743  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____46750  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____46757  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____46764  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____46771  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____46778  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____46785  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____46792  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____46799  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____46806  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____46813  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46822  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____46829  -> get_use_tactics () 
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu____46845  ->
    let uu____46846 = get_using_facts_from ()  in
    match uu____46846 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____46900  ->
    let uu____46901 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____46901
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____46912  ->
    let uu____46913 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____46913 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____46921 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____46932  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____46939  ->
    let uu____46940 = get_smt ()  in
    match uu____46940 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____46958  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____46965  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____46972  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____46979  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____46986  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____46993  ->
    (get_use_two_phase_tc ()) &&
      (let uu____46995 = lax ()  in Prims.op_Negation uu____46995)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____47003  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____47010  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____47017  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____47024  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____47031  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____47048 =
      let uu____47050 = trace_error ()  in Prims.op_Negation uu____47050  in
    if uu____47048
    then
      (push ();
       (let r =
          try
            (fun uu___1009_47065  ->
               match () with
               | () -> let uu____47070 = f ()  in FStar_Util.Inr uu____47070)
              ()
          with | uu___1008_47072 -> FStar_Util.Inl uu___1008_47072  in
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
        | (uu____47153,[]) -> true
        | (m2::ms,p::ps) ->
            (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
        | uu____47186 -> false  in
      let uu____47198 =
        FStar_All.pipe_right setting
          (FStar_Util.try_find
             (fun uu____47240  ->
                match uu____47240 with
                | (path,uu____47251) -> matches_path m_components path))
         in
      match uu____47198 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____47270,flag) -> flag
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____47299 = get_extract ()  in
    match uu____47299 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____47314 =
            let uu____47330 = get_no_extract ()  in
            let uu____47334 = get_extract_namespace ()  in
            let uu____47338 = get_extract_module ()  in
            (uu____47330, uu____47334, uu____47338)  in
          match uu____47314 with
          | ([],[],[]) -> ()
          | uu____47363 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         module_matches_namespace_filter m1 extract_setting)
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____47392 = get_extract_namespace ()  in
          match uu____47392 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____47420 = get_extract_module ()  in
          match uu____47420 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____47442 = no_extract m1  in Prims.op_Negation uu____47442)
          &&
          (let uu____47445 =
             let uu____47456 = get_extract_namespace ()  in
             let uu____47460 = get_extract_module ()  in
             (uu____47456, uu____47460)  in
           (match uu____47445 with
            | ([],[]) -> true
            | uu____47480 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  
let (should_be_already_cached : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____47500 = get_already_cached ()  in
    match uu____47500 with
    | FStar_Pervasives_Native.None  -> false
    | FStar_Pervasives_Native.Some already_cached_setting ->
        module_matches_namespace_filter m already_cached_setting
  
let (error_flags : unit -> error_flag Prims.list) =
  let cache = FStar_Util.smap_create (Prims.parse_int "10")  in
  fun uu____47533  ->
    let we = warn_error ()  in
    let uu____47536 = FStar_Util.smap_try_find cache we  in
    match uu____47536 with
    | FStar_Pervasives_Native.None  ->
        let r = parse_warn_error we  in (FStar_Util.smap_add cache we r; r)
    | FStar_Pervasives_Native.Some r -> r
  