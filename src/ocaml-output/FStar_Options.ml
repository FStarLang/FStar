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
    match projectee with | Low  -> true | uu____34742 -> false
  
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____34753 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | High  -> true | uu____34764 -> false
  
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____34775 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____34788 -> false
  
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
    match projectee with | Bool _0 -> true | uu____34843 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____34867 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____34891 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____34915 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____34940 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____34965 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _34973  -> Bool _34973 
let (mk_string : Prims.string -> option_val) = fun _34980  -> String _34980 
let (mk_path : Prims.string -> option_val) = fun _34987  -> Path _34987 
let (mk_int : Prims.int -> option_val) = fun _34994  -> Int _34994 
let (mk_list : option_val Prims.list -> option_val) =
  fun _35002  -> List _35002 
type options =
  | Set 
  | Reset 
  | Restore 
let (uu___is_Set : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Set  -> true | uu____35012 -> false
  
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____35023 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____35034 -> false
  
type error_flag =
  | CFatal 
  | CAlwaysError 
  | CError 
  | CWarning 
  | CSilent 
let (uu___is_CFatal : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CFatal  -> true | uu____35045 -> false
  
let (uu___is_CAlwaysError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CAlwaysError  -> true | uu____35056 -> false
  
let (uu___is_CError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CError  -> true | uu____35067 -> false
  
let (uu___is_CWarning : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CWarning  -> true | uu____35078 -> false
  
let (uu___is_CSilent : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CSilent  -> true | uu____35089 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____35114  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____35141  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____35169  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___289_35198  ->
    match uu___289_35198 with
    | Bool b -> b
    | uu____35202 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___290_35211  ->
    match uu___290_35211 with
    | Int b -> b
    | uu____35215 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___291_35224  ->
    match uu___291_35224 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____35230 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___292_35240  ->
    match uu___292_35240 with
    | List ts -> ts
    | uu____35246 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____35257 .
    (option_val -> 'Auu____35257) -> option_val -> 'Auu____35257 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____35275 = as_list' x  in
      FStar_All.pipe_right uu____35275 (FStar_List.map as_t)
  
let as_option :
  'Auu____35289 .
    (option_val -> 'Auu____35289) ->
      option_val -> 'Auu____35289 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___293_35304  ->
      match uu___293_35304 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____35308 = as_t v1  in
          FStar_Pervasives_Native.Some uu____35308
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___294_35317  ->
    match uu___294_35317 with
    | List ls ->
        let uu____35324 =
          FStar_List.map
            (fun l  ->
               let uu____35336 = as_string l  in
               FStar_Util.split uu____35336 ",") ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____35324
    | uu____35348 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let copy_optionstate :
  'Auu____35360 .
    'Auu____35360 FStar_Util.smap -> 'Auu____35360 FStar_Util.smap
  = fun m  -> FStar_Util.smap_copy m 
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (internal_peek : unit -> optionstate) =
  fun uu____35401  ->
    let uu____35402 =
      let uu____35405 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____35405  in
    FStar_List.hd uu____35402
  
let (peek : unit -> optionstate) = fun uu____35444  -> internal_peek () 
let (pop : unit -> unit) =
  fun uu____35450  ->
    let uu____35451 = FStar_ST.op_Bang fstar_options  in
    match uu____35451 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____35486::[] -> failwith "TOO MANY POPS!"
    | uu____35494::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____35536  ->
    let uu____35537 =
      let uu____35542 =
        let uu____35545 =
          let uu____35548 = FStar_ST.op_Bang fstar_options  in
          FStar_List.hd uu____35548  in
        FStar_List.map copy_optionstate uu____35545  in
      let uu____35582 = FStar_ST.op_Bang fstar_options  in uu____35542 ::
        uu____35582
       in
    FStar_ST.op_Colon_Equals fstar_options uu____35537
  
let (internal_pop : unit -> Prims.bool) =
  fun uu____35649  ->
    let curstack =
      let uu____35653 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____35653  in
    match curstack with
    | [] -> failwith "impossible: empty current option stack"
    | uu____35690::[] -> false
    | uu____35692::tl1 ->
        ((let uu____35697 =
            let uu____35702 =
              let uu____35707 = FStar_ST.op_Bang fstar_options  in
              FStar_List.tl uu____35707  in
            tl1 :: uu____35702  in
          FStar_ST.op_Colon_Equals fstar_options uu____35697);
         true)
  
let (internal_push : unit -> unit) =
  fun uu____35776  ->
    let curstack =
      let uu____35780 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____35780  in
    let stack' =
      let uu____35817 =
        let uu____35818 = FStar_List.hd curstack  in
        copy_optionstate uu____35818  in
      uu____35817 :: curstack  in
    let uu____35821 =
      let uu____35826 =
        let uu____35831 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____35831  in
      stack' :: uu____35826  in
    FStar_ST.op_Colon_Equals fstar_options uu____35821
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____35900 = FStar_ST.op_Bang fstar_options  in
    match uu____35900 with
    | [] -> failwith "set on empty option stack"
    | []::uu____35935 -> failwith "set on empty current option stack"
    | (uu____35943::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
  
let (snapshot : unit -> (Prims.int * unit)) =
  fun uu____35993  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____36023 = peek ()  in FStar_Util.smap_add uu____36023 k v1
  
let (set_option' : (Prims.string * option_val) -> unit) =
  fun uu____36036  -> match uu____36036 with | (k,v1) -> set_option k v1 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____36075 =
      let uu____36079 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____36079
       in
    FStar_ST.op_Colon_Equals light_off_files uu____36075
  
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
    let uu____37049 = FStar_ST.op_Bang r  in
    match uu____37049 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some f)
    | uu____37184 -> failwith "Multiple initialization of FStar.Options"  in
  let get1 uu____37205 =
    let uu____37206 = FStar_ST.op_Bang r  in
    match uu____37206 with
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
    let uu____37367 = FStar_Pervasives_Native.snd parse_warn_error_set_get ()
       in
    uu____37367 s
  
let (init : unit -> unit) =
  fun uu____37398  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____37418  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____37491 =
      let uu____37494 = peek ()  in FStar_Util.smap_try_find uu____37494 s
       in
    match uu____37491 with
    | FStar_Pervasives_Native.None  ->
        let uu____37497 =
          let uu____37499 = FStar_String.op_Hat s " not found"  in
          FStar_String.op_Hat "Impossible: option " uu____37499  in
        failwith uu____37497
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____37511 .
    Prims.string -> (option_val -> 'Auu____37511) -> 'Auu____37511
  = fun s  -> fun c  -> let uu____37529 = get_option s  in c uu____37529 
let (get_abort_on : unit -> Prims.int) =
  fun uu____37536  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____37545  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____37556  -> lookup_opt "admit_except" (as_option as_string) 
let (get_already_cached :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____37572  ->
    lookup_opt "already_cached" (as_option (as_list as_string))
  
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____37589  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37600  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____37612  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____37621  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37632  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____37646  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____37660  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____37674  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____37685  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37696  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____37708  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____37717  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____37726  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____37737  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____37749  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____37758  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____37771  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____37790  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____37804  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____37816  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____37825  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____37834  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37845  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____37857  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____37866  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____37877  -> lookup_opt "include" (as_list as_string) 
let (get_print : unit -> Prims.bool) =
  fun uu____37889  -> lookup_opt "print" as_bool 
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____37898  -> lookup_opt "print_in_place" as_bool 
let (get_profile : unit -> Prims.bool) =
  fun uu____37907  -> lookup_opt "profile" as_bool 
let (get_protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____37916  -> lookup_opt "protect_top_level_axioms" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____37925  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____37934  -> lookup_opt "initial_ifuel" as_int 
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu____37943  -> lookup_opt "keep_query_captions" as_bool 
let (get_lax : unit -> Prims.bool) =
  fun uu____37952  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____37963  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____37975  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____37984  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____37993  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____38002  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____38011  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____38020  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____38029  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____38038  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____38049  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____38061  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____38070  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____38079  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____38088  ->
    lookup_opt "normalize_pure_terms_for_extraction" as_bool
  
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38099  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____38111  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38122  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____38134  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____38143  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____38152  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____38161  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____38170  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____38179  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____38188  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____38197  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____38206  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38217  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____38229  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38240  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____38252  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____38261  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____38270  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____38279  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____38288  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____38297  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____38306  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____38315  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____38324  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____38333  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____38342  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____38351  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____38360  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____38369  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____38378  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____38387  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____38396  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38407  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____38419  ->
    let uu____38420 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____38420
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____38434  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38453  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____38467  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____38481  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____38493  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____38502  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____38513  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____38525  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____38534  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____38543  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____38552  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____38561  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____38570  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____38579  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____38588  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____38597  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____38606  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___295_38615  ->
    match uu___295_38615 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____38636 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____38645 = get_debug_level ()  in
    FStar_All.pipe_right uu____38645
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "<not set>" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____38811  ->
    let uu____38812 =
      let uu____38814 = FStar_ST.op_Bang _version  in
      let uu____38837 = FStar_ST.op_Bang _platform  in
      let uu____38860 = FStar_ST.op_Bang _compiler  in
      let uu____38883 = FStar_ST.op_Bang _date  in
      let uu____38906 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____38814
        uu____38837 uu____38860 uu____38883 uu____38906
       in
    FStar_Util.print_string uu____38812
  
let display_usage_aux :
  'Auu____38937 'Auu____38938 .
    ('Auu____38937 * Prims.string * 'Auu____38938 FStar_Getopt.opt_variant *
      Prims.string) Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____38993  ->
         match uu____38993 with
         | (uu____39006,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____39025 =
                      let uu____39027 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____39027  in
                    FStar_Util.print_string uu____39025
                  else
                    (let uu____39032 =
                       let uu____39034 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____39034 doc  in
                     FStar_Util.print_string uu____39032)
              | FStar_Getopt.OneArg (uu____39037,argname) ->
                  if doc = ""
                  then
                    let uu____39052 =
                      let uu____39054 = FStar_Util.colorize_bold flag  in
                      let uu____39056 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____39054
                        uu____39056
                       in
                    FStar_Util.print_string uu____39052
                  else
                    (let uu____39061 =
                       let uu____39063 = FStar_Util.colorize_bold flag  in
                       let uu____39065 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____39063
                         uu____39065 doc
                        in
                     FStar_Util.print_string uu____39061))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____39100 = o  in
    match uu____39100 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____39142 =
                let uu____39143 = f ()  in set_option name uu____39143  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____39164 = f x  in set_option name uu____39164
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____39191 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____39191  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____39217 =
        let uu____39220 = lookup_opt name as_list'  in
        FStar_List.append uu____39220 [value]  in
      mk_list uu____39217
  
let accumulate_string :
  'Auu____39234 .
    Prims.string -> ('Auu____39234 -> Prims.string) -> 'Auu____39234 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____39259 =
          let uu____39260 =
            let uu____39261 = post_processor value  in mk_string uu____39261
             in
          accumulated_option name uu____39260  in
        set_option name uu____39259
  
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
    match projectee with | Const _0 -> true | uu____39383 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____39404 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____39426 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____39439 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____39463 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____39489 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____39526 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____39577 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____39618 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____39638 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____39665 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____39709 -> true
    | uu____39712 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____39723 -> uu____39723
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___581_39747  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____39749 ->
                      let uu____39751 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____39751 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____39759 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____39759
                  | PathStr uu____39776 -> mk_path str_val
                  | SimpleStr uu____39778 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____39788 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____39805 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____39805
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
            let uu____39825 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____39825
  
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ  ->
    let desc_of_enum cases =
      let uu____39855 =
        let uu____39857 =
          FStar_String.op_Hat (FStar_String.concat "|" cases) "]"  in
        FStar_String.op_Hat "[" uu____39857  in
      FStar_Pervasives_Native.Some uu____39855  in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____39899,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____39909,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____39940 = desc_of_opt_type typ  in
      match uu____39940 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____39948  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____39974 =
      let uu____39976 = as_string s  in FStar_String.lowercase uu____39976
       in
    mk_string uu____39974
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string)
      Prims.list)
  =
  fun uu____40033  ->
    let uu____40047 =
      let uu____40061 =
        let uu____40075 =
          let uu____40089 =
            let uu____40103 =
              let uu____40115 =
                let uu____40116 = mk_bool true  in Const uu____40116  in
              (FStar_Getopt.noshort, "cache_checked_modules", uu____40115,
                "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
               in
            let uu____40123 =
              let uu____40137 =
                let uu____40151 =
                  let uu____40163 =
                    let uu____40164 = mk_bool true  in Const uu____40164  in
                  (FStar_Getopt.noshort, "cache_off", uu____40163,
                    "Do not read or write any .checked files")
                   in
                let uu____40171 =
                  let uu____40185 =
                    let uu____40197 =
                      let uu____40198 = mk_bool true  in Const uu____40198
                       in
                    (FStar_Getopt.noshort, "cmi", uu____40197,
                      "Inline across module interfaces during extraction (aka. cross-module inlining)")
                     in
                  let uu____40205 =
                    let uu____40219 =
                      let uu____40233 =
                        let uu____40247 =
                          let uu____40261 =
                            let uu____40275 =
                              let uu____40289 =
                                let uu____40303 =
                                  let uu____40315 =
                                    let uu____40316 = mk_bool true  in
                                    Const uu____40316  in
                                  (FStar_Getopt.noshort, "detail_errors",
                                    uu____40315,
                                    "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                   in
                                let uu____40323 =
                                  let uu____40337 =
                                    let uu____40349 =
                                      let uu____40350 = mk_bool true  in
                                      Const uu____40350  in
                                    (FStar_Getopt.noshort,
                                      "detail_hint_replay", uu____40349,
                                      "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                     in
                                  let uu____40357 =
                                    let uu____40371 =
                                      let uu____40383 =
                                        let uu____40384 = mk_bool true  in
                                        Const uu____40384  in
                                      (FStar_Getopt.noshort, "doc",
                                        uu____40383,
                                        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                       in
                                    let uu____40391 =
                                      let uu____40405 =
                                        let uu____40419 =
                                          let uu____40431 =
                                            let uu____40432 = mk_bool true
                                               in
                                            Const uu____40432  in
                                          (FStar_Getopt.noshort,
                                            "eager_inference", uu____40431,
                                            "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                           in
                                        let uu____40439 =
                                          let uu____40453 =
                                            let uu____40465 =
                                              let uu____40466 = mk_bool true
                                                 in
                                              Const uu____40466  in
                                            (FStar_Getopt.noshort,
                                              "eager_subtyping", uu____40465,
                                              "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                             in
                                          let uu____40473 =
                                            let uu____40487 =
                                              let uu____40501 =
                                                let uu____40515 =
                                                  let uu____40529 =
                                                    let uu____40541 =
                                                      let uu____40542 =
                                                        mk_bool true  in
                                                      Const uu____40542  in
                                                    (FStar_Getopt.noshort,
                                                      "expose_interfaces",
                                                      uu____40541,
                                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                     in
                                                  let uu____40549 =
                                                    let uu____40563 =
                                                      let uu____40575 =
                                                        let uu____40576 =
                                                          mk_bool true  in
                                                        Const uu____40576  in
                                                      (FStar_Getopt.noshort,
                                                        "hide_uvar_nums",
                                                        uu____40575,
                                                        "Don't print unification variable numbers")
                                                       in
                                                    let uu____40583 =
                                                      let uu____40597 =
                                                        let uu____40611 =
                                                          let uu____40623 =
                                                            let uu____40624 =
                                                              mk_bool true
                                                               in
                                                            Const uu____40624
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "hint_info",
                                                            uu____40623,
                                                            "Print information regarding hints (deprecated; use --query_stats instead)")
                                                           in
                                                        let uu____40631 =
                                                          let uu____40645 =
                                                            let uu____40657 =
                                                              let uu____40658
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____40658
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "in",
                                                              uu____40657,
                                                              "Legacy interactive mode; reads input from stdin")
                                                             in
                                                          let uu____40665 =
                                                            let uu____40679 =
                                                              let uu____40691
                                                                =
                                                                let uu____40692
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____40692
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "ide",
                                                                uu____40691,
                                                                "JSON-based interactive mode for IDEs")
                                                               in
                                                            let uu____40699 =
                                                              let uu____40713
                                                                =
                                                                let uu____40727
                                                                  =
                                                                  let uu____40739
                                                                    =
                                                                    let uu____40740
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40740
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "print",
                                                                    uu____40739,
                                                                    "Parses and prettyprints the files included on the command line")
                                                                   in
                                                                let uu____40747
                                                                  =
                                                                  let uu____40761
                                                                    =
                                                                    let uu____40773
                                                                    =
                                                                    let uu____40774
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40774
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_in_place",
                                                                    uu____40773,
                                                                    "Parses and prettyprints in place the files included on the command line")
                                                                     in
                                                                  let uu____40781
                                                                    =
                                                                    let uu____40795
                                                                    =
                                                                    let uu____40807
                                                                    =
                                                                    let uu____40808
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40808
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "profile",
                                                                    uu____40807,
                                                                    "Prints timing information for various operations in the compiler")
                                                                     in
                                                                    let uu____40815
                                                                    =
                                                                    let uu____40829
                                                                    =
                                                                    let uu____40843
                                                                    =
                                                                    let uu____40857
                                                                    =
                                                                    let uu____40871
                                                                    =
                                                                    let uu____40885
                                                                    =
                                                                    let uu____40897
                                                                    =
                                                                    let uu____40898
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40898
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____40897,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____40905
                                                                    =
                                                                    let uu____40919
                                                                    =
                                                                    let uu____40933
                                                                    =
                                                                    let uu____40945
                                                                    =
                                                                    let uu____40946
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40946
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____40945,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____40953
                                                                    =
                                                                    let uu____40967
                                                                    =
                                                                    let uu____40979
                                                                    =
                                                                    let uu____40980
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40980
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____40979,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____40987
                                                                    =
                                                                    let uu____41001
                                                                    =
                                                                    let uu____41015
                                                                    =
                                                                    let uu____41029
                                                                    =
                                                                    let uu____41043
                                                                    =
                                                                    let uu____41055
                                                                    =
                                                                    let uu____41056
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41056
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____41055,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____41063
                                                                    =
                                                                    let uu____41077
                                                                    =
                                                                    let uu____41091
                                                                    =
                                                                    let uu____41103
                                                                    =
                                                                    let uu____41104
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41104
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____41103,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____41111
                                                                    =
                                                                    let uu____41125
                                                                    =
                                                                    let uu____41139
                                                                    =
                                                                    let uu____41151
                                                                    =
                                                                    let uu____41152
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41152
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____41151,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____41159
                                                                    =
                                                                    let uu____41173
                                                                    =
                                                                    let uu____41185
                                                                    =
                                                                    let uu____41186
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41186
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____41185,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____41193
                                                                    =
                                                                    let uu____41207
                                                                    =
                                                                    let uu____41219
                                                                    =
                                                                    let uu____41220
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41220
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____41219,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____41227
                                                                    =
                                                                    let uu____41241
                                                                    =
                                                                    let uu____41255
                                                                    =
                                                                    let uu____41269
                                                                    =
                                                                    let uu____41281
                                                                    =
                                                                    let uu____41282
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41282
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____41281,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____41289
                                                                    =
                                                                    let uu____41303
                                                                    =
                                                                    let uu____41315
                                                                    =
                                                                    let uu____41316
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41316
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____41315,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____41323
                                                                    =
                                                                    let uu____41337
                                                                    =
                                                                    let uu____41349
                                                                    =
                                                                    let uu____41350
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41350
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____41349,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____41357
                                                                    =
                                                                    let uu____41371
                                                                    =
                                                                    let uu____41383
                                                                    =
                                                                    let uu____41384
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41384
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____41383,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____41391
                                                                    =
                                                                    let uu____41405
                                                                    =
                                                                    let uu____41417
                                                                    =
                                                                    let uu____41418
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41418
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____41417,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____41425
                                                                    =
                                                                    let uu____41439
                                                                    =
                                                                    let uu____41451
                                                                    =
                                                                    let uu____41452
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41452
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____41451,
                                                                    "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)")
                                                                     in
                                                                    let uu____41459
                                                                    =
                                                                    let uu____41473
                                                                    =
                                                                    let uu____41485
                                                                    =
                                                                    let uu____41486
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41486
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____41485,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____41493
                                                                    =
                                                                    let uu____41507
                                                                    =
                                                                    let uu____41519
                                                                    =
                                                                    let uu____41520
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41520
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____41519,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____41527
                                                                    =
                                                                    let uu____41541
                                                                    =
                                                                    let uu____41553
                                                                    =
                                                                    let uu____41554
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41554
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____41553,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____41561
                                                                    =
                                                                    let uu____41575
                                                                    =
                                                                    let uu____41589
                                                                    =
                                                                    let uu____41601
                                                                    =
                                                                    let uu____41602
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41602
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____41601,
                                                                    "Disable all non-critical output")
                                                                     in
                                                                    let uu____41609
                                                                    =
                                                                    let uu____41623
                                                                    =
                                                                    let uu____41637
                                                                    =
                                                                    let uu____41651
                                                                    =
                                                                    let uu____41665
                                                                    =
                                                                    let uu____41679
                                                                    =
                                                                    let uu____41691
                                                                    =
                                                                    let uu____41692
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41692
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____41691,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____41699
                                                                    =
                                                                    let uu____41713
                                                                    =
                                                                    let uu____41725
                                                                    =
                                                                    let uu____41726
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41726
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____41725,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____41733
                                                                    =
                                                                    let uu____41747
                                                                    =
                                                                    let uu____41759
                                                                    =
                                                                    let uu____41760
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41760
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____41759,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____41767
                                                                    =
                                                                    let uu____41781
                                                                    =
                                                                    let uu____41793
                                                                    =
                                                                    let uu____41794
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41794
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____41793,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____41801
                                                                    =
                                                                    let uu____41815
                                                                    =
                                                                    let uu____41829
                                                                    =
                                                                    let uu____41841
                                                                    =
                                                                    let uu____41842
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41842
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____41841,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____41849
                                                                    =
                                                                    let uu____41863
                                                                    =
                                                                    let uu____41877
                                                                    =
                                                                    let uu____41889
                                                                    =
                                                                    let uu____41890
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41890
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____41889,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____41897
                                                                    =
                                                                    let uu____41911
                                                                    =
                                                                    let uu____41923
                                                                    =
                                                                    let uu____41924
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41924
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____41923,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____41931
                                                                    =
                                                                    let uu____41945
                                                                    =
                                                                    let uu____41957
                                                                    =
                                                                    let uu____41958
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41958
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____41957,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____41965
                                                                    =
                                                                    let uu____41979
                                                                    =
                                                                    let uu____41991
                                                                    =
                                                                    let uu____41992
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41992
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____41991,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____41999
                                                                    =
                                                                    let uu____42013
                                                                    =
                                                                    let uu____42025
                                                                    =
                                                                    let uu____42026
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42026
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____42025,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____42033
                                                                    =
                                                                    let uu____42047
                                                                    =
                                                                    let uu____42059
                                                                    =
                                                                    let uu____42060
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42060
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____42059,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____42067
                                                                    =
                                                                    let uu____42081
                                                                    =
                                                                    let uu____42093
                                                                    =
                                                                    let uu____42094
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42094
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____42093,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____42101
                                                                    =
                                                                    let uu____42115
                                                                    =
                                                                    let uu____42127
                                                                    =
                                                                    let uu____42128
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42128
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____42127,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____42135
                                                                    =
                                                                    let uu____42149
                                                                    =
                                                                    let uu____42163
                                                                    =
                                                                    let uu____42175
                                                                    =
                                                                    let uu____42176
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42176
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____42175,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____42183
                                                                    =
                                                                    let uu____42197
                                                                    =
                                                                    let uu____42209
                                                                    =
                                                                    let uu____42210
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42210
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____42209,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____42217
                                                                    =
                                                                    let uu____42231
                                                                    =
                                                                    let uu____42245
                                                                    =
                                                                    let uu____42259
                                                                    =
                                                                    let uu____42273
                                                                    =
                                                                    let uu____42285
                                                                    =
                                                                    let uu____42286
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42286
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____42285,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____42293
                                                                    =
                                                                    let uu____42307
                                                                    =
                                                                    let uu____42319
                                                                    =
                                                                    let uu____42320
                                                                    =
                                                                    let uu____42328
                                                                    =
                                                                    let uu____42329
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42329
                                                                     in
                                                                    ((fun
                                                                    uu____42336
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____42328)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42320
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____42319,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____42345
                                                                    =
                                                                    let uu____42359
                                                                    =
                                                                    let uu____42371
                                                                    =
                                                                    let uu____42372
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42372
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____42371,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____42379
                                                                    =
                                                                    let uu____42393
                                                                    =
                                                                    let uu____42407
                                                                    =
                                                                    let uu____42419
                                                                    =
                                                                    let uu____42420
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42420
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____42419,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____42427
                                                                    =
                                                                    let uu____42441
                                                                    =
                                                                    let uu____42455
                                                                    =
                                                                    let uu____42469
                                                                    =
                                                                    let uu____42483
                                                                    =
                                                                    let uu____42497
                                                                    =
                                                                    let uu____42509
                                                                    =
                                                                    let uu____42510
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42510
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____42509,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____42517
                                                                    =
                                                                    let uu____42531
                                                                    =
                                                                    let uu____42543
                                                                    =
                                                                    let uu____42544
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42544
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____42543,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____42551
                                                                    =
                                                                    let uu____42565
                                                                    =
                                                                    let uu____42579
                                                                    =
                                                                    let uu____42593
                                                                    =
                                                                    let uu____42607
                                                                    =
                                                                    let uu____42619
                                                                    =
                                                                    let uu____42620
                                                                    =
                                                                    let uu____42628
                                                                    =
                                                                    let uu____42629
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42629
                                                                     in
                                                                    ((fun
                                                                    uu____42635
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____42628)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42620
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____42619,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____42663
                                                                    =
                                                                    let uu____42677
                                                                    =
                                                                    let uu____42689
                                                                    =
                                                                    let uu____42690
                                                                    =
                                                                    let uu____42698
                                                                    =
                                                                    let uu____42699
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42699
                                                                     in
                                                                    ((fun
                                                                    uu____42705
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____42698)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42690
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____42689,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____42733
                                                                    =
                                                                    let uu____42747
                                                                    =
                                                                    let uu____42759
                                                                    =
                                                                    let uu____42760
                                                                    =
                                                                    let uu____42768
                                                                    =
                                                                    let uu____42769
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42769
                                                                     in
                                                                    ((fun
                                                                    uu____42776
                                                                     ->
                                                                    (
                                                                    let uu____42778
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____42778);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____42768)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42760
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____42759,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____42747]
                                                                     in
                                                                    uu____42677
                                                                    ::
                                                                    uu____42733
                                                                     in
                                                                    uu____42607
                                                                    ::
                                                                    uu____42663
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____42593
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____42579
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____42565
                                                                     in
                                                                    uu____42531
                                                                    ::
                                                                    uu____42551
                                                                     in
                                                                    uu____42497
                                                                    ::
                                                                    uu____42517
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____42483
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____42469
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____42455
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____42441
                                                                     in
                                                                    uu____42407
                                                                    ::
                                                                    uu____42427
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____42393
                                                                     in
                                                                    uu____42359
                                                                    ::
                                                                    uu____42379
                                                                     in
                                                                    uu____42307
                                                                    ::
                                                                    uu____42345
                                                                     in
                                                                    uu____42273
                                                                    ::
                                                                    uu____42293
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____42259
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____42245
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____42231
                                                                     in
                                                                    uu____42197
                                                                    ::
                                                                    uu____42217
                                                                     in
                                                                    uu____42163
                                                                    ::
                                                                    uu____42183
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____42149
                                                                     in
                                                                    uu____42115
                                                                    ::
                                                                    uu____42135
                                                                     in
                                                                    uu____42081
                                                                    ::
                                                                    uu____42101
                                                                     in
                                                                    uu____42047
                                                                    ::
                                                                    uu____42067
                                                                     in
                                                                    uu____42013
                                                                    ::
                                                                    uu____42033
                                                                     in
                                                                    uu____41979
                                                                    ::
                                                                    uu____41999
                                                                     in
                                                                    uu____41945
                                                                    ::
                                                                    uu____41965
                                                                     in
                                                                    uu____41911
                                                                    ::
                                                                    uu____41931
                                                                     in
                                                                    uu____41877
                                                                    ::
                                                                    uu____41897
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____41863
                                                                     in
                                                                    uu____41829
                                                                    ::
                                                                    uu____41849
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____41815
                                                                     in
                                                                    uu____41781
                                                                    ::
                                                                    uu____41801
                                                                     in
                                                                    uu____41747
                                                                    ::
                                                                    uu____41767
                                                                     in
                                                                    uu____41713
                                                                    ::
                                                                    uu____41733
                                                                     in
                                                                    uu____41679
                                                                    ::
                                                                    uu____41699
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____41665
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____41651
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____41637
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____41623
                                                                     in
                                                                    uu____41589
                                                                    ::
                                                                    uu____41609
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____41575
                                                                     in
                                                                    uu____41541
                                                                    ::
                                                                    uu____41561
                                                                     in
                                                                    uu____41507
                                                                    ::
                                                                    uu____41527
                                                                     in
                                                                    uu____41473
                                                                    ::
                                                                    uu____41493
                                                                     in
                                                                    uu____41439
                                                                    ::
                                                                    uu____41459
                                                                     in
                                                                    uu____41405
                                                                    ::
                                                                    uu____41425
                                                                     in
                                                                    uu____41371
                                                                    ::
                                                                    uu____41391
                                                                     in
                                                                    uu____41337
                                                                    ::
                                                                    uu____41357
                                                                     in
                                                                    uu____41303
                                                                    ::
                                                                    uu____41323
                                                                     in
                                                                    uu____41269
                                                                    ::
                                                                    uu____41289
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____41255
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____41241
                                                                     in
                                                                    uu____41207
                                                                    ::
                                                                    uu____41227
                                                                     in
                                                                    uu____41173
                                                                    ::
                                                                    uu____41193
                                                                     in
                                                                    uu____41139
                                                                    ::
                                                                    uu____41159
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____41125
                                                                     in
                                                                    uu____41091
                                                                    ::
                                                                    uu____41111
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____41077
                                                                     in
                                                                    uu____41043
                                                                    ::
                                                                    uu____41063
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____41029
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____41015
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____41001
                                                                     in
                                                                    uu____40967
                                                                    ::
                                                                    uu____40987
                                                                     in
                                                                    uu____40933
                                                                    ::
                                                                    uu____40953
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____40919
                                                                     in
                                                                    uu____40885
                                                                    ::
                                                                    uu____40905
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    "Retain comments in the logged SMT queries (requires --log_queries; default true)")
                                                                    ::
                                                                    uu____40871
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____40857
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try initially (default 2)")
                                                                    ::
                                                                    uu____40843
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "protect_top_level_axioms",
                                                                    BoolStr,
                                                                    "Guard nullary top-level symbols in the SMT encoding from provide ambient ground facts (default 'true')")
                                                                    ::
                                                                    uu____40829
                                                                     in
                                                                    uu____40795
                                                                    ::
                                                                    uu____40815
                                                                     in
                                                                  uu____40761
                                                                    ::
                                                                    uu____40781
                                                                   in
                                                                uu____40727
                                                                  ::
                                                                  uu____40747
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "include",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "path")),
                                                                "A directory in which to search for files included on the command line")
                                                                ::
                                                                uu____40713
                                                               in
                                                            uu____40679 ::
                                                              uu____40699
                                                             in
                                                          uu____40645 ::
                                                            uu____40665
                                                           in
                                                        uu____40611 ::
                                                          uu____40631
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "hint_file",
                                                        (PathStr "path"),
                                                        "Read/write hints to <path> (instead of module-specific hints files)")
                                                        :: uu____40597
                                                       in
                                                    uu____40563 ::
                                                      uu____40583
                                                     in
                                                  uu____40529 :: uu____40549
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "extract_namespace",
                                                  (Accumulated
                                                     (PostProcessed
                                                        (pp_lowercase,
                                                          (SimpleStr
                                                             "namespace name")))),
                                                  "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                  :: uu____40515
                                                 in
                                              (FStar_Getopt.noshort,
                                                "extract_module",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "module_name")))),
                                                "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                                :: uu____40501
                                               in
                                            (FStar_Getopt.noshort, "extract",
                                              (Accumulated
                                                 (SimpleStr
                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                              "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                              :: uu____40487
                                             in
                                          uu____40453 :: uu____40473  in
                                        uu____40419 :: uu____40439  in
                                      (FStar_Getopt.noshort, "dump_module",
                                        (Accumulated
                                           (SimpleStr "module_name")), "")
                                        :: uu____40405
                                       in
                                    uu____40371 :: uu____40391  in
                                  uu____40337 :: uu____40357  in
                                uu____40303 :: uu____40323  in
                              (FStar_Getopt.noshort, "dep",
                                (EnumStr ["make"; "graph"; "full"; "raw"]),
                                "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                                :: uu____40289
                               in
                            (FStar_Getopt.noshort, "defensive",
                              (EnumStr ["no"; "warn"; "fail"]),
                              "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                              :: uu____40275
                             in
                          (FStar_Getopt.noshort, "debug_level",
                            (Accumulated
                               (OpenEnumStr
                                  (["Low"; "Medium"; "High"; "Extreme"],
                                    "..."))),
                            "Control the verbosity of debugging info") ::
                            uu____40261
                           in
                        (FStar_Getopt.noshort, "debug",
                          (Accumulated (SimpleStr "module_name")),
                          "Print lots of debugging information while checking module")
                          :: uu____40247
                         in
                      (FStar_Getopt.noshort, "codegen-lib",
                        (Accumulated (SimpleStr "namespace")),
                        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                        :: uu____40233
                       in
                    (FStar_Getopt.noshort, "codegen",
                      (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                      "Generate code for further compilation to executable code, or build a compiler plugin")
                      :: uu____40219
                     in
                  uu____40185 :: uu____40205  in
                uu____40151 :: uu____40171  in
              (FStar_Getopt.noshort, "cache_dir",
                (PostProcessed (pp_validate_dir, (PathStr "dir"))),
                "Read and write .checked and .checked.lax in directory <dir>")
                :: uu____40137
               in
            uu____40103 :: uu____40123  in
          (FStar_Getopt.noshort, "already_cached",
            (Accumulated
               (SimpleStr
                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
            "\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")
            :: uu____40089
           in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____40075
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____40061
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___296_44326  ->
             match uu___296_44326 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____40047

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____44355  ->
    let uu____44358 = specs_with_types ()  in
    FStar_List.map
      (fun uu____44389  ->
         match uu____44389 with
         | (short,long,typ,doc) ->
             let uu____44411 =
               let uu____44425 = arg_spec_of_opt_type long typ  in
               (short, long, uu____44425, doc)  in
             mk_spec uu____44411) uu____44358

let (settable : Prims.string -> Prims.bool) =
  fun uu___297_44440  ->
    match uu___297_44440 with
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
    | uu____44563 -> false
  
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
       (fun uu____44662  ->
          match uu____44662 with
          | (uu____44677,x,uu____44679,uu____44680) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____44755  ->
          match uu____44755 with
          | (uu____44770,x,uu____44772,uu____44773) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____44789  ->
    let uu____44790 = specs ()  in display_usage_aux uu____44790
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____44822 -> true
    | uu____44825 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____44836 -> uu____44836
  
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
        (fun uu___759_44857  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____44874 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____44874
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____44910  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____44916 =
             let uu____44920 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____44920 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____44916)
       in
    let uu____44977 =
      let uu____44981 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____44981
       in
    (res, uu____44977)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____45023  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____45066 = specs ()  in
       FStar_Getopt.parse_cmdline uu____45066 (fun x  -> ())  in
     (let uu____45073 =
        let uu____45079 =
          let uu____45080 = FStar_List.map mk_string old_verify_module  in
          List uu____45080  in
        ("verify_module", uu____45079)  in
      set_option' uu____45073);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____45099 =
        let uu____45101 =
          let uu____45103 =
            let uu____45105 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____45105  in
          (FStar_String.length f1) - uu____45103  in
        uu____45101 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____45099  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____45118 = get_lax ()  in
    if uu____45118
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____45139 = module_name_of_file_name fn  in
    should_verify uu____45139
  
let (module_name_eq : Prims.string -> Prims.string -> Prims.bool) =
  fun m1  ->
    fun m2  -> (FStar_String.lowercase m1) = (FStar_String.lowercase m2)
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____45167 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____45167 (FStar_List.existsb (module_name_eq m))
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____45185 = should_verify m  in
    if uu____45185 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____45202  ->
    let cache_dir =
      let uu____45207 = get_cache_dir ()  in
      match uu____45207 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some c -> [c]  in
    let uu____45221 = get_no_default_includes ()  in
    if uu____45221
    then
      let uu____45227 = get_include ()  in
      FStar_List.append cache_dir uu____45227
    else
      (let lib_paths =
         let uu____45238 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____45238 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = FStar_String.op_Hat fstar_bin_directory "/.."
                in
             let defs = universe_include_path_base_dirs  in
             let uu____45254 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> FStar_String.op_Hat fstar_home x))
                in
             FStar_All.pipe_right uu____45254
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____45281 =
         let uu____45285 =
           let uu____45289 = get_include ()  in
           FStar_List.append uu____45289 ["."]  in
         FStar_List.append lib_paths uu____45285  in
       FStar_List.append cache_dir uu____45281)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____45316 = FStar_Util.smap_try_find file_map filename  in
    match uu____45316 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___810_45338  ->
               match () with
               | () ->
                   let uu____45342 = FStar_Util.is_path_absolute filename  in
                   if uu____45342
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____45358 =
                        let uu____45362 = include_path ()  in
                        FStar_List.rev uu____45362  in
                      FStar_Util.find_map uu____45358
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___809_45390 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____45410  ->
    let uu____45411 = get_prims ()  in
    match uu____45411 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____45420 = find_file filename  in
        (match uu____45420 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____45429 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____45429)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____45442  ->
    let uu____45443 = prims ()  in FStar_Util.basename uu____45443
  
let (pervasives : unit -> Prims.string) =
  fun uu____45451  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____45455 = find_file filename  in
    match uu____45455 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____45464 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____45464
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____45474  ->
    let uu____45475 = pervasives ()  in FStar_Util.basename uu____45475
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____45483  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____45487 = find_file filename  in
    match uu____45487 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____45496 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____45496
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____45509 = get_odir ()  in
    match uu____45509 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____45527 = get_cache_dir ()  in
    match uu____45527 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____45536 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____45536
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns  ->
    let cache = FStar_Util.smap_create (Prims.parse_int "31")  in
    let with_cache f s =
      let uu____45658 = FStar_Util.smap_try_find cache s  in
      match uu____45658 with
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
             let uu____45793 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____45793  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____45816 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              let s1 = FStar_Util.trim_string s  in
              if s1 = ""
              then []
              else
                with_cache
                  (fun s2  ->
                     let uu____45884 =
                       FStar_All.pipe_right (FStar_Util.splitlines s2)
                         (FStar_List.concatMap
                            (fun s3  -> FStar_Util.split s3 " "))
                        in
                     FStar_All.pipe_right uu____45884
                       (FStar_List.map parse_one_setting)) s1))
       in
    FStar_All.pipe_right uu____45816 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____45959 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____45959 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____45974  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____45983  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____45992  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____45999  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____46006  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____46013  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____46023 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____46034 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____46045 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____46056 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____46065  ->
    let uu____46066 = get_codegen ()  in
    FStar_Util.map_opt uu____46066
      (fun uu___298_46072  ->
         match uu___298_46072 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____46078 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____46091  ->
    let uu____46092 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____46092
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____46118  -> let uu____46119 = get_debug ()  in uu____46119 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____46136 = get_debug ()  in
    FStar_All.pipe_right uu____46136
      (FStar_List.existsb (module_name_eq modul))
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____46161 = get_debug ()  in
       FStar_All.pipe_right uu____46161
         (FStar_List.existsb (module_name_eq modul)))
        && (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____46176  ->
    let uu____46177 = get_defensive ()  in uu____46177 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____46187  ->
    let uu____46188 = get_defensive ()  in uu____46188 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46200  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____46207  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____46214  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____46221  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____46231 = get_dump_module ()  in
    FStar_All.pipe_right uu____46231 (FStar_List.existsb (module_name_eq s))
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____46246  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____46253  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____46263 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____46263
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____46299  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____46307  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____46314  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46323  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____46330  -> get_ide () 
let (print : unit -> Prims.bool) = fun uu____46337  -> get_print () 
let (print_in_place : unit -> Prims.bool) =
  fun uu____46344  -> get_print_in_place () 
let profile : 'a . (unit -> 'a) -> ('a -> Prims.string) -> 'a =
  fun f  ->
    fun msg  ->
      let uu____46375 = get_profile ()  in
      if uu____46375
      then
        let uu____46378 = FStar_Util.record_time f  in
        match uu____46378 with
        | (a,time) ->
            ((let uu____46389 = FStar_Util.string_of_int time  in
              let uu____46391 = msg a  in
              FStar_Util.print2 "Elapsed time %s ms: %s\n" uu____46389
                uu____46391);
             a)
      else f ()
  
let (protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____46402  -> get_protect_top_level_axioms () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____46409  ->
    let uu____46410 = get_initial_fuel ()  in
    let uu____46412 = get_max_fuel ()  in Prims.min uu____46410 uu____46412
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____46420  ->
    let uu____46421 = get_initial_ifuel ()  in
    let uu____46423 = get_max_ifuel ()  in Prims.min uu____46421 uu____46423
  
let (interactive : unit -> Prims.bool) =
  fun uu____46431  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____46438  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____46447  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____46454  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____46461  -> get_log_queries () 
let (keep_query_captions : unit -> Prims.bool) =
  fun uu____46468  -> (log_queries ()) && (get_keep_query_captions ()) 
let (log_types : unit -> Prims.bool) = fun uu____46475  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____46482  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____46489  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____46496  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____46503  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____46509  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____46518  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____46525  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____46535 = get_no_extract ()  in
    FStar_All.pipe_right uu____46535 (FStar_List.existsb (module_name_eq s))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____46550  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____46557  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____46564  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____46571  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46580  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____46587  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____46594  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____46601  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____46608  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____46615  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____46622  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____46629  -> get_print_z3_statistics () 
let (query_stats : unit -> Prims.bool) =
  fun uu____46636  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____46643  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46652  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____46659  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____46666  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____46673  ->
    let uu____46674 = get_smtencoding_nl_arith_repr ()  in
    uu____46674 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____46684  ->
    let uu____46685 = get_smtencoding_nl_arith_repr ()  in
    uu____46685 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____46695  ->
    let uu____46696 = get_smtencoding_nl_arith_repr ()  in
    uu____46696 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____46706  ->
    let uu____46707 = get_smtencoding_l_arith_repr ()  in
    uu____46707 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____46717  ->
    let uu____46718 = get_smtencoding_l_arith_repr ()  in
    uu____46718 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____46728  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____46735  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____46742  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____46749  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____46756  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____46763  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____46770  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____46777  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____46784  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____46791  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____46798  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____46805  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____46812  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____46819  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46828  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____46835  -> get_use_tactics () 
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu____46851  ->
    let uu____46852 = get_using_facts_from ()  in
    match uu____46852 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____46906  ->
    let uu____46907 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____46907
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____46918  ->
    let uu____46919 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____46919 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____46927 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____46938  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____46945  ->
    let uu____46946 = get_smt ()  in
    match uu____46946 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____46964  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____46971  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____46978  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____46985  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____46992  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____46999  ->
    (get_use_two_phase_tc ()) &&
      (let uu____47001 = lax ()  in Prims.op_Negation uu____47001)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____47009  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____47016  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____47023  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____47030  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____47037  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____47054 =
      let uu____47056 = trace_error ()  in Prims.op_Negation uu____47056  in
    if uu____47054
    then
      (push ();
       (let r =
          try
            (fun uu___1009_47071  ->
               match () with
               | () -> let uu____47076 = f ()  in FStar_Util.Inr uu____47076)
              ()
          with | uu___1008_47078 -> FStar_Util.Inl uu___1008_47078  in
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
        | (uu____47159,[]) -> true
        | (m2::ms,p::ps) ->
            (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
        | uu____47192 -> false  in
      let uu____47204 =
        FStar_All.pipe_right setting
          (FStar_Util.try_find
             (fun uu____47246  ->
                match uu____47246 with
                | (path,uu____47257) -> matches_path m_components path))
         in
      match uu____47204 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____47276,flag) -> flag
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____47305 = get_extract ()  in
    match uu____47305 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____47320 =
            let uu____47336 = get_no_extract ()  in
            let uu____47340 = get_extract_namespace ()  in
            let uu____47344 = get_extract_module ()  in
            (uu____47336, uu____47340, uu____47344)  in
          match uu____47320 with
          | ([],[],[]) -> ()
          | uu____47369 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         module_matches_namespace_filter m1 extract_setting)
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____47398 = get_extract_namespace ()  in
          match uu____47398 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____47426 = get_extract_module ()  in
          match uu____47426 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____47448 = no_extract m1  in Prims.op_Negation uu____47448)
          &&
          (let uu____47451 =
             let uu____47462 = get_extract_namespace ()  in
             let uu____47466 = get_extract_module ()  in
             (uu____47462, uu____47466)  in
           (match uu____47451 with
            | ([],[]) -> true
            | uu____47486 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  
let (should_be_already_cached : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____47506 = get_already_cached ()  in
    match uu____47506 with
    | FStar_Pervasives_Native.None  -> false
    | FStar_Pervasives_Native.Some already_cached_setting ->
        module_matches_namespace_filter m already_cached_setting
  
let (error_flags : unit -> error_flag Prims.list) =
  let cache = FStar_Util.smap_create (Prims.parse_int "10")  in
  fun uu____47539  ->
    let we = warn_error ()  in
    let uu____47542 = FStar_Util.smap_try_find cache we  in
    match uu____47542 with
    | FStar_Pervasives_Native.None  ->
        let r = parse_warn_error we  in (FStar_Util.smap_add cache we r; r)
    | FStar_Pervasives_Native.Some r -> r
  