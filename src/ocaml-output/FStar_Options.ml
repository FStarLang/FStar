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
  
type error_flag =
  | CFatal 
  | CAlwaysError 
  | CError 
  | CWarning 
  | CSilent 
let (uu___is_CFatal : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CFatal  -> true | uu____369 -> false
  
let (uu___is_CAlwaysError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CAlwaysError  -> true | uu____380 -> false
  
let (uu___is_CError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CError  -> true | uu____391 -> false
  
let (uu___is_CWarning : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CWarning  -> true | uu____402 -> false
  
let (uu___is_CSilent : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CSilent  -> true | uu____413 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____438  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____465  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____493  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___11_522  ->
    match uu___11_522 with
    | Bool b -> b
    | uu____526 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___12_535  ->
    match uu___12_535 with
    | Int b -> b
    | uu____539 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___13_548  ->
    match uu___13_548 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____554 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___14_564  ->
    match uu___14_564 with
    | List ts -> ts
    | uu____570 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____581 .
    (option_val -> 'Auu____581) -> option_val -> 'Auu____581 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____599 = as_list' x  in
      FStar_All.pipe_right uu____599 (FStar_List.map as_t)
  
let as_option :
  'Auu____613 .
    (option_val -> 'Auu____613) ->
      option_val -> 'Auu____613 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___15_628  ->
      match uu___15_628 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____632 = as_t v1  in FStar_Pervasives_Native.Some uu____632
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___16_641  ->
    match uu___16_641 with
    | List ls ->
        let uu____648 =
          FStar_List.map
            (fun l  ->
               let uu____660 = as_string l  in FStar_Util.split uu____660 ",")
            ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____648
    | uu____672 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let copy_optionstate :
  'Auu____684 . 'Auu____684 FStar_Util.smap -> 'Auu____684 FStar_Util.smap =
  fun m  -> FStar_Util.smap_copy m 
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (internal_peek : unit -> optionstate) =
  fun uu____725  ->
    let uu____726 =
      let uu____729 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____729  in
    FStar_List.hd uu____726
  
let (peek : unit -> optionstate) = fun uu____768  -> internal_peek () 
let (pop : unit -> unit) =
  fun uu____774  ->
    let uu____775 = FStar_ST.op_Bang fstar_options  in
    match uu____775 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____810::[] -> failwith "TOO MANY POPS!"
    | uu____818::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____860  ->
    let uu____861 =
      let uu____866 =
        let uu____869 =
          let uu____872 = FStar_ST.op_Bang fstar_options  in
          FStar_List.hd uu____872  in
        FStar_List.map copy_optionstate uu____869  in
      let uu____906 = FStar_ST.op_Bang fstar_options  in uu____866 ::
        uu____906
       in
    FStar_ST.op_Colon_Equals fstar_options uu____861
  
let (internal_pop : unit -> Prims.bool) =
  fun uu____973  ->
    let curstack =
      let uu____977 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____977  in
    match curstack with
    | [] -> failwith "impossible: empty current option stack"
    | uu____1014::[] -> false
    | uu____1016::tl1 ->
        ((let uu____1021 =
            let uu____1026 =
              let uu____1031 = FStar_ST.op_Bang fstar_options  in
              FStar_List.tl uu____1031  in
            tl1 :: uu____1026  in
          FStar_ST.op_Colon_Equals fstar_options uu____1021);
         true)
  
let (internal_push : unit -> unit) =
  fun uu____1100  ->
    let curstack =
      let uu____1104 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____1104  in
    let stack' =
      let uu____1141 =
        let uu____1142 = FStar_List.hd curstack  in
        copy_optionstate uu____1142  in
      uu____1141 :: curstack  in
    let uu____1145 =
      let uu____1150 =
        let uu____1155 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____1155  in
      stack' :: uu____1150  in
    FStar_ST.op_Colon_Equals fstar_options uu____1145
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____1224 = FStar_ST.op_Bang fstar_options  in
    match uu____1224 with
    | [] -> failwith "set on empty option stack"
    | []::uu____1259 -> failwith "set on empty current option stack"
    | (uu____1267::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
  
let (snapshot : unit -> (Prims.int * unit)) =
  fun uu____1317  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____1347 = peek ()  in FStar_Util.smap_add uu____1347 k v1
  
let (set_option' : (Prims.string * option_val) -> unit) =
  fun uu____1360  -> match uu____1360 with | (k,v1) -> set_option k v1 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____1399 =
      let uu____1403 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____1403
       in
    FStar_ST.op_Colon_Equals light_off_files uu____1399
  
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
    let uu____2373 = FStar_ST.op_Bang r  in
    match uu____2373 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some f)
    | uu____2508 -> failwith "Multiple initialization of FStar.Options"  in
  let get1 uu____2529 =
    let uu____2530 = FStar_ST.op_Bang r  in
    match uu____2530 with
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
    let uu____2691 = FStar_Pervasives_Native.snd parse_warn_error_set_get ()
       in
    uu____2691 s
  
let (init : unit -> unit) =
  fun uu____2722  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____2742  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____2815 =
      let uu____2818 = peek ()  in FStar_Util.smap_try_find uu____2818 s  in
    match uu____2815 with
    | FStar_Pervasives_Native.None  ->
        let uu____2821 =
          let uu____2823 = FStar_String.op_Hat s " not found"  in
          FStar_String.op_Hat "Impossible: option " uu____2823  in
        failwith uu____2821
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____2835 . Prims.string -> (option_val -> 'Auu____2835) -> 'Auu____2835
  = fun s  -> fun c  -> let uu____2853 = get_option s  in c uu____2853 
let (get_abort_on : unit -> Prims.int) =
  fun uu____2860  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____2869  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____2880  -> lookup_opt "admit_except" (as_option as_string) 
let (get_already_cached :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2896  ->
    lookup_opt "already_cached" (as_option (as_list as_string))
  
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____2913  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2924  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____2936  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____2945  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2956  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____2970  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____2984  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____2998  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____3009  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3020  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____3032  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____3041  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____3050  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____3061  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____3073  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____3082  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____3095  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____3114  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____3128  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____3140  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____3149  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____3158  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3169  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____3181  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____3190  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____3201  -> lookup_opt "include" (as_list as_string) 
let (get_print : unit -> Prims.bool) =
  fun uu____3213  -> lookup_opt "print" as_bool 
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____3222  -> lookup_opt "print_in_place" as_bool 
let (get_profile : unit -> Prims.bool) =
  fun uu____3231  -> lookup_opt "profile" as_bool 
let (get_protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____3240  -> lookup_opt "protect_top_level_axioms" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____3249  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____3258  -> lookup_opt "initial_ifuel" as_int 
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu____3267  -> lookup_opt "keep_query_captions" as_bool 
let (get_lax : unit -> Prims.bool) =
  fun uu____3276  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____3287  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____3299  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____3308  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____3317  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____3326  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____3335  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____3344  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____3353  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____3362  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____3373  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____3385  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____3394  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____3403  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____3412  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3423  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____3435  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3446  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____3458  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____3467  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____3476  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____3485  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____3494  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____3503  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____3512  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____3521  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____3530  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3541  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____3553  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3564  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____3576  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____3585  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____3594  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____3603  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____3612  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____3621  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____3630  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____3639  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____3648  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____3657  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____3666  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____3675  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____3684  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____3693  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____3702  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____3711  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____3720  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3731  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____3743  ->
    let uu____3744 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____3744
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____3758  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3777  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____3791  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____3805  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____3817  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____3826  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____3837  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____3849  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____3858  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____3867  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____3876  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____3885  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____3894  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____3903  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____3912  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____3921  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____3930  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___17_3939  ->
    match uu___17_3939 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____3960 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____3969 = get_debug_level ()  in
    FStar_All.pipe_right uu____3969
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "<not set>" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____4135  ->
    let uu____4136 =
      let uu____4138 = FStar_ST.op_Bang _version  in
      let uu____4161 = FStar_ST.op_Bang _platform  in
      let uu____4184 = FStar_ST.op_Bang _compiler  in
      let uu____4207 = FStar_ST.op_Bang _date  in
      let uu____4230 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____4138
        uu____4161 uu____4184 uu____4207 uu____4230
       in
    FStar_Util.print_string uu____4136
  
let display_usage_aux :
  'Auu____4261 'Auu____4262 .
    ('Auu____4261 * Prims.string * 'Auu____4262 FStar_Getopt.opt_variant *
      Prims.string) Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____4317  ->
         match uu____4317 with
         | (uu____4330,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____4349 =
                      let uu____4351 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____4351  in
                    FStar_Util.print_string uu____4349
                  else
                    (let uu____4356 =
                       let uu____4358 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____4358 doc  in
                     FStar_Util.print_string uu____4356)
              | FStar_Getopt.OneArg (uu____4361,argname) ->
                  if doc = ""
                  then
                    let uu____4376 =
                      let uu____4378 = FStar_Util.colorize_bold flag  in
                      let uu____4380 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____4378 uu____4380
                       in
                    FStar_Util.print_string uu____4376
                  else
                    (let uu____4385 =
                       let uu____4387 = FStar_Util.colorize_bold flag  in
                       let uu____4389 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____4387
                         uu____4389 doc
                        in
                     FStar_Util.print_string uu____4385))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____4424 = o  in
    match uu____4424 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____4466 =
                let uu____4467 = f ()  in set_option name uu____4467  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____4488 = f x  in set_option name uu____4488
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____4515 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____4515  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____4541 =
        let uu____4544 = lookup_opt name as_list'  in
        FStar_List.append uu____4544 [value]  in
      mk_list uu____4541
  
let accumulate_string :
  'Auu____4558 .
    Prims.string -> ('Auu____4558 -> Prims.string) -> 'Auu____4558 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____4583 =
          let uu____4584 =
            let uu____4585 = post_processor value  in mk_string uu____4585
             in
          accumulated_option name uu____4584  in
        set_option name uu____4583
  
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
    match projectee with | Const _0 -> true | uu____4707 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____4728 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____4750 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____4763 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____4787 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____4813 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____4850 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____4901 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____4942 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____4962 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____4989 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____5033 -> true
    | uu____5036 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____5047 -> uu____5047
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___22_5071  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____5073 ->
                      let uu____5075 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____5075 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____5083 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____5083
                  | PathStr uu____5100 -> mk_path str_val
                  | SimpleStr uu____5102 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____5112 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____5129 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____5129
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
            let uu____5149 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____5149
  
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ  ->
    let desc_of_enum cases =
      let uu____5179 =
        let uu____5181 =
          FStar_String.op_Hat (FStar_String.concat "|" cases) "]"  in
        FStar_String.op_Hat "[" uu____5181  in
      FStar_Pervasives_Native.Some uu____5179  in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____5223,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____5233,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____5264 = desc_of_opt_type typ  in
      match uu____5264 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____5272  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____5298 =
      let uu____5300 = as_string s  in FStar_String.lowercase uu____5300  in
    mk_string uu____5298
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string)
      Prims.list)
  =
  fun uu____5357  ->
    let uu____5371 =
      let uu____5385 =
        let uu____5399 =
          let uu____5413 =
            let uu____5427 =
              let uu____5439 =
                let uu____5440 = mk_bool true  in Const uu____5440  in
              (FStar_Getopt.noshort, "cache_checked_modules", uu____5439,
                "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
               in
            let uu____5447 =
              let uu____5461 =
                let uu____5475 =
                  let uu____5487 =
                    let uu____5488 = mk_bool true  in Const uu____5488  in
                  (FStar_Getopt.noshort, "cache_off", uu____5487,
                    "Do not read or write any .checked files")
                   in
                let uu____5495 =
                  let uu____5509 =
                    let uu____5521 =
                      let uu____5522 = mk_bool true  in Const uu____5522  in
                    (FStar_Getopt.noshort, "cmi", uu____5521,
                      "Inline across module interfaces during extraction (aka. cross-module inlining)")
                     in
                  let uu____5529 =
                    let uu____5543 =
                      let uu____5557 =
                        let uu____5571 =
                          let uu____5585 =
                            let uu____5599 =
                              let uu____5613 =
                                let uu____5627 =
                                  let uu____5639 =
                                    let uu____5640 = mk_bool true  in
                                    Const uu____5640  in
                                  (FStar_Getopt.noshort, "detail_errors",
                                    uu____5639,
                                    "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                   in
                                let uu____5647 =
                                  let uu____5661 =
                                    let uu____5673 =
                                      let uu____5674 = mk_bool true  in
                                      Const uu____5674  in
                                    (FStar_Getopt.noshort,
                                      "detail_hint_replay", uu____5673,
                                      "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                     in
                                  let uu____5681 =
                                    let uu____5695 =
                                      let uu____5707 =
                                        let uu____5708 = mk_bool true  in
                                        Const uu____5708  in
                                      (FStar_Getopt.noshort, "doc",
                                        uu____5707,
                                        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                       in
                                    let uu____5715 =
                                      let uu____5729 =
                                        let uu____5743 =
                                          let uu____5755 =
                                            let uu____5756 = mk_bool true  in
                                            Const uu____5756  in
                                          (FStar_Getopt.noshort,
                                            "eager_inference", uu____5755,
                                            "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                           in
                                        let uu____5763 =
                                          let uu____5777 =
                                            let uu____5789 =
                                              let uu____5790 = mk_bool true
                                                 in
                                              Const uu____5790  in
                                            (FStar_Getopt.noshort,
                                              "eager_subtyping", uu____5789,
                                              "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                             in
                                          let uu____5797 =
                                            let uu____5811 =
                                              let uu____5825 =
                                                let uu____5839 =
                                                  let uu____5853 =
                                                    let uu____5865 =
                                                      let uu____5866 =
                                                        mk_bool true  in
                                                      Const uu____5866  in
                                                    (FStar_Getopt.noshort,
                                                      "expose_interfaces",
                                                      uu____5865,
                                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                     in
                                                  let uu____5873 =
                                                    let uu____5887 =
                                                      let uu____5899 =
                                                        let uu____5900 =
                                                          mk_bool true  in
                                                        Const uu____5900  in
                                                      (FStar_Getopt.noshort,
                                                        "hide_uvar_nums",
                                                        uu____5899,
                                                        "Don't print unification variable numbers")
                                                       in
                                                    let uu____5907 =
                                                      let uu____5921 =
                                                        let uu____5935 =
                                                          let uu____5947 =
                                                            let uu____5948 =
                                                              mk_bool true
                                                               in
                                                            Const uu____5948
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "hint_info",
                                                            uu____5947,
                                                            "Print information regarding hints (deprecated; use --query_stats instead)")
                                                           in
                                                        let uu____5955 =
                                                          let uu____5969 =
                                                            let uu____5981 =
                                                              let uu____5982
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____5982
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "in",
                                                              uu____5981,
                                                              "Legacy interactive mode; reads input from stdin")
                                                             in
                                                          let uu____5989 =
                                                            let uu____6003 =
                                                              let uu____6015
                                                                =
                                                                let uu____6016
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____6016
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "ide",
                                                                uu____6015,
                                                                "JSON-based interactive mode for IDEs")
                                                               in
                                                            let uu____6023 =
                                                              let uu____6037
                                                                =
                                                                let uu____6051
                                                                  =
                                                                  let uu____6063
                                                                    =
                                                                    let uu____6064
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6064
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "print",
                                                                    uu____6063,
                                                                    "Parses and prettyprints the files included on the command line")
                                                                   in
                                                                let uu____6071
                                                                  =
                                                                  let uu____6085
                                                                    =
                                                                    let uu____6097
                                                                    =
                                                                    let uu____6098
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6098
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_in_place",
                                                                    uu____6097,
                                                                    "Parses and prettyprints in place the files included on the command line")
                                                                     in
                                                                  let uu____6105
                                                                    =
                                                                    let uu____6119
                                                                    =
                                                                    let uu____6131
                                                                    =
                                                                    let uu____6132
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6132
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "profile",
                                                                    uu____6131,
                                                                    "Prints timing information for various operations in the compiler")
                                                                     in
                                                                    let uu____6139
                                                                    =
                                                                    let uu____6153
                                                                    =
                                                                    let uu____6167
                                                                    =
                                                                    let uu____6181
                                                                    =
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
                                                                    "lax",
                                                                    uu____6221,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____6229
                                                                    =
                                                                    let uu____6243
                                                                    =
                                                                    let uu____6257
                                                                    =
                                                                    let uu____6269
                                                                    =
                                                                    let uu____6270
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6270
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____6269,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____6277
                                                                    =
                                                                    let uu____6291
                                                                    =
                                                                    let uu____6303
                                                                    =
                                                                    let uu____6304
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6304
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____6303,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____6311
                                                                    =
                                                                    let uu____6325
                                                                    =
                                                                    let uu____6339
                                                                    =
                                                                    let uu____6353
                                                                    =
                                                                    let uu____6367
                                                                    =
                                                                    let uu____6379
                                                                    =
                                                                    let uu____6380
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6380
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____6379,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____6387
                                                                    =
                                                                    let uu____6401
                                                                    =
                                                                    let uu____6415
                                                                    =
                                                                    let uu____6427
                                                                    =
                                                                    let uu____6428
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6428
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____6427,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____6435
                                                                    =
                                                                    let uu____6449
                                                                    =
                                                                    let uu____6463
                                                                    =
                                                                    let uu____6475
                                                                    =
                                                                    let uu____6476
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6476
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____6475,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____6483
                                                                    =
                                                                    let uu____6497
                                                                    =
                                                                    let uu____6509
                                                                    =
                                                                    let uu____6510
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6510
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____6509,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____6517
                                                                    =
                                                                    let uu____6531
                                                                    =
                                                                    let uu____6543
                                                                    =
                                                                    let uu____6544
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6544
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____6543,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____6551
                                                                    =
                                                                    let uu____6565
                                                                    =
                                                                    let uu____6579
                                                                    =
                                                                    let uu____6593
                                                                    =
                                                                    let uu____6605
                                                                    =
                                                                    let uu____6606
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6606
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____6605,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____6613
                                                                    =
                                                                    let uu____6627
                                                                    =
                                                                    let uu____6639
                                                                    =
                                                                    let uu____6640
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6640
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____6639,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____6647
                                                                    =
                                                                    let uu____6661
                                                                    =
                                                                    let uu____6673
                                                                    =
                                                                    let uu____6674
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6674
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____6673,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____6681
                                                                    =
                                                                    let uu____6695
                                                                    =
                                                                    let uu____6707
                                                                    =
                                                                    let uu____6708
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6708
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____6707,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____6715
                                                                    =
                                                                    let uu____6729
                                                                    =
                                                                    let uu____6741
                                                                    =
                                                                    let uu____6742
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6742
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____6741,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____6749
                                                                    =
                                                                    let uu____6763
                                                                    =
                                                                    let uu____6775
                                                                    =
                                                                    let uu____6776
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6776
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____6775,
                                                                    "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)")
                                                                     in
                                                                    let uu____6783
                                                                    =
                                                                    let uu____6797
                                                                    =
                                                                    let uu____6809
                                                                    =
                                                                    let uu____6810
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6810
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____6809,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____6817
                                                                    =
                                                                    let uu____6831
                                                                    =
                                                                    let uu____6843
                                                                    =
                                                                    let uu____6844
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6844
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____6843,
                                                                    "Print SMT query statistics")
                                                                     in
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
                                                                    "record_hints",
                                                                    uu____6877,
                                                                    "Record a database of hints for efficient proof replay")
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
                                                                    "silent",
                                                                    uu____6925,
                                                                    "Disable all non-critical output")
                                                                     in
                                                                    let uu____6933
                                                                    =
                                                                    let uu____6947
                                                                    =
                                                                    let uu____6961
                                                                    =
                                                                    let uu____6975
                                                                    =
                                                                    let uu____6989
                                                                    =
                                                                    let uu____7003
                                                                    =
                                                                    let uu____7015
                                                                    =
                                                                    let uu____7016
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7016
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____7015,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____7023
                                                                    =
                                                                    let uu____7037
                                                                    =
                                                                    let uu____7049
                                                                    =
                                                                    let uu____7050
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7050
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____7049,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____7057
                                                                    =
                                                                    let uu____7071
                                                                    =
                                                                    let uu____7083
                                                                    =
                                                                    let uu____7084
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7084
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____7083,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____7091
                                                                    =
                                                                    let uu____7105
                                                                    =
                                                                    let uu____7117
                                                                    =
                                                                    let uu____7118
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7118
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____7117,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____7125
                                                                    =
                                                                    let uu____7139
                                                                    =
                                                                    let uu____7153
                                                                    =
                                                                    let uu____7165
                                                                    =
                                                                    let uu____7166
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7166
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____7165,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____7173
                                                                    =
                                                                    let uu____7187
                                                                    =
                                                                    let uu____7201
                                                                    =
                                                                    let uu____7213
                                                                    =
                                                                    let uu____7214
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7214
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____7213,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____7221
                                                                    =
                                                                    let uu____7235
                                                                    =
                                                                    let uu____7247
                                                                    =
                                                                    let uu____7248
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7248
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____7247,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____7255
                                                                    =
                                                                    let uu____7269
                                                                    =
                                                                    let uu____7281
                                                                    =
                                                                    let uu____7282
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7282
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____7281,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____7289
                                                                    =
                                                                    let uu____7303
                                                                    =
                                                                    let uu____7315
                                                                    =
                                                                    let uu____7316
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7316
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____7315,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____7323
                                                                    =
                                                                    let uu____7337
                                                                    =
                                                                    let uu____7349
                                                                    =
                                                                    let uu____7350
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7350
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____7349,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____7357
                                                                    =
                                                                    let uu____7371
                                                                    =
                                                                    let uu____7383
                                                                    =
                                                                    let uu____7384
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7384
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____7383,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____7391
                                                                    =
                                                                    let uu____7405
                                                                    =
                                                                    let uu____7417
                                                                    =
                                                                    let uu____7418
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7418
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____7417,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____7425
                                                                    =
                                                                    let uu____7439
                                                                    =
                                                                    let uu____7451
                                                                    =
                                                                    let uu____7452
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7452
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____7451,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____7459
                                                                    =
                                                                    let uu____7473
                                                                    =
                                                                    let uu____7487
                                                                    =
                                                                    let uu____7499
                                                                    =
                                                                    let uu____7500
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7500
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____7499,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____7507
                                                                    =
                                                                    let uu____7521
                                                                    =
                                                                    let uu____7533
                                                                    =
                                                                    let uu____7534
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7534
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____7533,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____7541
                                                                    =
                                                                    let uu____7555
                                                                    =
                                                                    let uu____7569
                                                                    =
                                                                    let uu____7583
                                                                    =
                                                                    let uu____7597
                                                                    =
                                                                    let uu____7609
                                                                    =
                                                                    let uu____7610
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7610
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____7609,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____7617
                                                                    =
                                                                    let uu____7631
                                                                    =
                                                                    let uu____7643
                                                                    =
                                                                    let uu____7644
                                                                    =
                                                                    let uu____7652
                                                                    =
                                                                    let uu____7653
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7653
                                                                     in
                                                                    ((fun
                                                                    uu____7660
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____7652)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7644
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____7643,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____7669
                                                                    =
                                                                    let uu____7683
                                                                    =
                                                                    let uu____7695
                                                                    =
                                                                    let uu____7696
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7696
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____7695,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____7703
                                                                    =
                                                                    let uu____7717
                                                                    =
                                                                    let uu____7731
                                                                    =
                                                                    let uu____7743
                                                                    =
                                                                    let uu____7744
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7744
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____7743,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____7751
                                                                    =
                                                                    let uu____7765
                                                                    =
                                                                    let uu____7779
                                                                    =
                                                                    let uu____7793
                                                                    =
                                                                    let uu____7807
                                                                    =
                                                                    let uu____7821
                                                                    =
                                                                    let uu____7833
                                                                    =
                                                                    let uu____7834
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7834
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____7833,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____7841
                                                                    =
                                                                    let uu____7855
                                                                    =
                                                                    let uu____7867
                                                                    =
                                                                    let uu____7868
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7868
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____7867,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____7875
                                                                    =
                                                                    let uu____7889
                                                                    =
                                                                    let uu____7903
                                                                    =
                                                                    let uu____7917
                                                                    =
                                                                    let uu____7931
                                                                    =
                                                                    let uu____7943
                                                                    =
                                                                    let uu____7944
                                                                    =
                                                                    let uu____7952
                                                                    =
                                                                    let uu____7953
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7953
                                                                     in
                                                                    ((fun
                                                                    uu____7959
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____7952)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7944
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____7943,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____7987
                                                                    =
                                                                    let uu____8001
                                                                    =
                                                                    let uu____8013
                                                                    =
                                                                    let uu____8014
                                                                    =
                                                                    let uu____8022
                                                                    =
                                                                    let uu____8023
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____8023
                                                                     in
                                                                    ((fun
                                                                    uu____8029
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____8022)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____8014
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____8013,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____8057
                                                                    =
                                                                    let uu____8071
                                                                    =
                                                                    let uu____8083
                                                                    =
                                                                    let uu____8084
                                                                    =
                                                                    let uu____8092
                                                                    =
                                                                    let uu____8093
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____8093
                                                                     in
                                                                    ((fun
                                                                    uu____8100
                                                                     ->
                                                                    (
                                                                    let uu____8102
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____8102);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____8092)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____8084
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____8083,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____8071]
                                                                     in
                                                                    uu____8001
                                                                    ::
                                                                    uu____8057
                                                                     in
                                                                    uu____7931
                                                                    ::
                                                                    uu____7987
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____7917
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____7903
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____7889
                                                                     in
                                                                    uu____7855
                                                                    ::
                                                                    uu____7875
                                                                     in
                                                                    uu____7821
                                                                    ::
                                                                    uu____7841
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____7807
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____7793
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____7779
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____7765
                                                                     in
                                                                    uu____7731
                                                                    ::
                                                                    uu____7751
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____7717
                                                                     in
                                                                    uu____7683
                                                                    ::
                                                                    uu____7703
                                                                     in
                                                                    uu____7631
                                                                    ::
                                                                    uu____7669
                                                                     in
                                                                    uu____7597
                                                                    ::
                                                                    uu____7617
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____7583
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____7569
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____7555
                                                                     in
                                                                    uu____7521
                                                                    ::
                                                                    uu____7541
                                                                     in
                                                                    uu____7487
                                                                    ::
                                                                    uu____7507
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____7473
                                                                     in
                                                                    uu____7439
                                                                    ::
                                                                    uu____7459
                                                                     in
                                                                    uu____7405
                                                                    ::
                                                                    uu____7425
                                                                     in
                                                                    uu____7371
                                                                    ::
                                                                    uu____7391
                                                                     in
                                                                    uu____7337
                                                                    ::
                                                                    uu____7357
                                                                     in
                                                                    uu____7303
                                                                    ::
                                                                    uu____7323
                                                                     in
                                                                    uu____7269
                                                                    ::
                                                                    uu____7289
                                                                     in
                                                                    uu____7235
                                                                    ::
                                                                    uu____7255
                                                                     in
                                                                    uu____7201
                                                                    ::
                                                                    uu____7221
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____7187
                                                                     in
                                                                    uu____7153
                                                                    ::
                                                                    uu____7173
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____7139
                                                                     in
                                                                    uu____7105
                                                                    ::
                                                                    uu____7125
                                                                     in
                                                                    uu____7071
                                                                    ::
                                                                    uu____7091
                                                                     in
                                                                    uu____7037
                                                                    ::
                                                                    uu____7057
                                                                     in
                                                                    uu____7003
                                                                    ::
                                                                    uu____7023
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6989
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6975
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____6961
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____6947
                                                                     in
                                                                    uu____6913
                                                                    ::
                                                                    uu____6933
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____6899
                                                                     in
                                                                    uu____6865
                                                                    ::
                                                                    uu____6885
                                                                     in
                                                                    uu____6831
                                                                    ::
                                                                    uu____6851
                                                                     in
                                                                    uu____6797
                                                                    ::
                                                                    uu____6817
                                                                     in
                                                                    uu____6763
                                                                    ::
                                                                    uu____6783
                                                                     in
                                                                    uu____6729
                                                                    ::
                                                                    uu____6749
                                                                     in
                                                                    uu____6695
                                                                    ::
                                                                    uu____6715
                                                                     in
                                                                    uu____6661
                                                                    ::
                                                                    uu____6681
                                                                     in
                                                                    uu____6627
                                                                    ::
                                                                    uu____6647
                                                                     in
                                                                    uu____6593
                                                                    ::
                                                                    uu____6613
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____6579
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____6565
                                                                     in
                                                                    uu____6531
                                                                    ::
                                                                    uu____6551
                                                                     in
                                                                    uu____6497
                                                                    ::
                                                                    uu____6517
                                                                     in
                                                                    uu____6463
                                                                    ::
                                                                    uu____6483
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____6449
                                                                     in
                                                                    uu____6415
                                                                    ::
                                                                    uu____6435
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____6401
                                                                     in
                                                                    uu____6367
                                                                    ::
                                                                    uu____6387
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____6353
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____6339
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____6325
                                                                     in
                                                                    uu____6291
                                                                    ::
                                                                    uu____6311
                                                                     in
                                                                    uu____6257
                                                                    ::
                                                                    uu____6277
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____6243
                                                                     in
                                                                    uu____6209
                                                                    ::
                                                                    uu____6229
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    "Retain comments in the logged SMT queries (requires --log_queries; default true)")
                                                                    ::
                                                                    uu____6195
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____6181
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try initially (default 2)")
                                                                    ::
                                                                    uu____6167
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "protect_top_level_axioms",
                                                                    BoolStr,
                                                                    "Guard nullary top-level symbols in the SMT encoding from provide ambient ground facts (default 'true')")
                                                                    ::
                                                                    uu____6153
                                                                     in
                                                                    uu____6119
                                                                    ::
                                                                    uu____6139
                                                                     in
                                                                  uu____6085
                                                                    ::
                                                                    uu____6105
                                                                   in
                                                                uu____6051 ::
                                                                  uu____6071
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "include",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "path")),
                                                                "A directory in which to search for files included on the command line")
                                                                :: uu____6037
                                                               in
                                                            uu____6003 ::
                                                              uu____6023
                                                             in
                                                          uu____5969 ::
                                                            uu____5989
                                                           in
                                                        uu____5935 ::
                                                          uu____5955
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "hint_file",
                                                        (PathStr "path"),
                                                        "Read/write hints to <path> (instead of module-specific hints files)")
                                                        :: uu____5921
                                                       in
                                                    uu____5887 :: uu____5907
                                                     in
                                                  uu____5853 :: uu____5873
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "extract_namespace",
                                                  (Accumulated
                                                     (PostProcessed
                                                        (pp_lowercase,
                                                          (SimpleStr
                                                             "namespace name")))),
                                                  "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                  :: uu____5839
                                                 in
                                              (FStar_Getopt.noshort,
                                                "extract_module",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "module_name")))),
                                                "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                                :: uu____5825
                                               in
                                            (FStar_Getopt.noshort, "extract",
                                              (Accumulated
                                                 (SimpleStr
                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                              "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                              :: uu____5811
                                             in
                                          uu____5777 :: uu____5797  in
                                        uu____5743 :: uu____5763  in
                                      (FStar_Getopt.noshort, "dump_module",
                                        (Accumulated
                                           (SimpleStr "module_name")), "")
                                        :: uu____5729
                                       in
                                    uu____5695 :: uu____5715  in
                                  uu____5661 :: uu____5681  in
                                uu____5627 :: uu____5647  in
                              (FStar_Getopt.noshort, "dep",
                                (EnumStr ["make"; "graph"; "full"; "raw"]),
                                "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                                :: uu____5613
                               in
                            (FStar_Getopt.noshort, "defensive",
                              (EnumStr ["no"; "warn"; "fail"]),
                              "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                              :: uu____5599
                             in
                          (FStar_Getopt.noshort, "debug_level",
                            (Accumulated
                               (OpenEnumStr
                                  (["Low"; "Medium"; "High"; "Extreme"],
                                    "..."))),
                            "Control the verbosity of debugging info") ::
                            uu____5585
                           in
                        (FStar_Getopt.noshort, "debug",
                          (Accumulated (SimpleStr "module_name")),
                          "Print lots of debugging information while checking module")
                          :: uu____5571
                         in
                      (FStar_Getopt.noshort, "codegen-lib",
                        (Accumulated (SimpleStr "namespace")),
                        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                        :: uu____5557
                       in
                    (FStar_Getopt.noshort, "codegen",
                      (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                      "Generate code for further compilation to executable code, or build a compiler plugin")
                      :: uu____5543
                     in
                  uu____5509 :: uu____5529  in
                uu____5475 :: uu____5495  in
              (FStar_Getopt.noshort, "cache_dir",
                (PostProcessed (pp_validate_dir, (PathStr "dir"))),
                "Read and write .checked and .checked.lax in directory <dir>")
                :: uu____5461
               in
            uu____5427 :: uu____5447  in
          (FStar_Getopt.noshort, "already_cached",
            (Accumulated
               (SimpleStr
                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
            "\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")
            :: uu____5413
           in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____5399
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____5385
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___18_9650  ->
             match uu___18_9650 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____5371

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____9679  ->
    let uu____9682 = specs_with_types ()  in
    FStar_List.map
      (fun uu____9713  ->
         match uu____9713 with
         | (short,long,typ,doc) ->
             let uu____9735 =
               let uu____9749 = arg_spec_of_opt_type long typ  in
               (short, long, uu____9749, doc)  in
             mk_spec uu____9735) uu____9682

let (settable : Prims.string -> Prims.bool) =
  fun uu___19_9764  ->
    match uu___19_9764 with
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
    | uu____9887 -> false
  
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
       (fun uu____9986  ->
          match uu____9986 with
          | (uu____10001,x,uu____10003,uu____10004) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____10079  ->
          match uu____10079 with
          | (uu____10094,x,uu____10096,uu____10097) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____10113  ->
    let uu____10114 = specs ()  in display_usage_aux uu____10114
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____10146 -> true
    | uu____10149 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____10160 -> uu____10160
  
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
        (fun uu___24_10181  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____10198 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____10198
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____10234  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____10240 =
             let uu____10244 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____10244 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____10240)
       in
    let uu____10301 =
      let uu____10305 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____10305
       in
    (res, uu____10301)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____10347  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____10390 = specs ()  in
       FStar_Getopt.parse_cmdline uu____10390 (fun x  -> ())  in
     (let uu____10397 =
        let uu____10403 =
          let uu____10404 = FStar_List.map mk_string old_verify_module  in
          List uu____10404  in
        ("verify_module", uu____10403)  in
      set_option' uu____10397);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____10423 =
        let uu____10425 =
          let uu____10427 =
            let uu____10429 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____10429  in
          (FStar_String.length f1) - uu____10427  in
        uu____10425 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____10423  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____10442 = get_lax ()  in
    if uu____10442
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____10463 = module_name_of_file_name fn  in
    should_verify uu____10463
  
let (module_name_eq : Prims.string -> Prims.string -> Prims.bool) =
  fun m1  ->
    fun m2  -> (FStar_String.lowercase m1) = (FStar_String.lowercase m2)
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____10491 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____10491 (FStar_List.existsb (module_name_eq m))
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____10509 = should_verify m  in
    if uu____10509 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____10526  ->
    let cache_dir =
      let uu____10531 = get_cache_dir ()  in
      match uu____10531 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some c -> [c]  in
    let uu____10545 = get_no_default_includes ()  in
    if uu____10545
    then
      let uu____10551 = get_include ()  in
      FStar_List.append cache_dir uu____10551
    else
      (let lib_paths =
         let uu____10562 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____10562 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = FStar_String.op_Hat fstar_bin_directory "/.."
                in
             let defs = universe_include_path_base_dirs  in
             let uu____10578 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> FStar_String.op_Hat fstar_home x))
                in
             FStar_All.pipe_right uu____10578
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____10605 =
         let uu____10609 =
           let uu____10613 = get_include ()  in
           FStar_List.append uu____10613 ["."]  in
         FStar_List.append lib_paths uu____10609  in
       FStar_List.append cache_dir uu____10605)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____10640 = FStar_Util.smap_try_find file_map filename  in
    match uu____10640 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___26_10662  ->
               match () with
               | () ->
                   let uu____10666 = FStar_Util.is_path_absolute filename  in
                   if uu____10666
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____10682 =
                        let uu____10686 = include_path ()  in
                        FStar_List.rev uu____10686  in
                      FStar_Util.find_map uu____10682
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___25_10714 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____10734  ->
    let uu____10735 = get_prims ()  in
    match uu____10735 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____10744 = find_file filename  in
        (match uu____10744 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____10753 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____10753)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____10766  ->
    let uu____10767 = prims ()  in FStar_Util.basename uu____10767
  
let (pervasives : unit -> Prims.string) =
  fun uu____10775  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____10779 = find_file filename  in
    match uu____10779 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____10788 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____10788
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____10798  ->
    let uu____10799 = pervasives ()  in FStar_Util.basename uu____10799
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____10807  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____10811 = find_file filename  in
    match uu____10811 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____10820 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____10820
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____10833 = get_odir ()  in
    match uu____10833 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____10851 = get_cache_dir ()  in
    match uu____10851 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____10860 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____10860
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns  ->
    let cache = FStar_Util.smap_create (Prims.parse_int "31")  in
    let with_cache f s =
      let uu____10982 = FStar_Util.smap_try_find cache s  in
      match uu____10982 with
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
             let uu____11117 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____11117  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____11140 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              let s1 = FStar_Util.trim_string s  in
              if s1 = ""
              then []
              else
                with_cache
                  (fun s2  ->
                     let uu____11208 =
                       FStar_All.pipe_right (FStar_Util.splitlines s2)
                         (FStar_List.concatMap
                            (fun s3  -> FStar_Util.split s3 " "))
                        in
                     FStar_All.pipe_right uu____11208
                       (FStar_List.map parse_one_setting)) s1))
       in
    FStar_All.pipe_right uu____11140 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____11283 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____11283 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____11298  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____11307  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11316  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____11323  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____11330  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____11337  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____11347 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____11358 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____11369 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____11380 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____11389  ->
    let uu____11390 = get_codegen ()  in
    FStar_Util.map_opt uu____11390
      (fun uu___20_11396  ->
         match uu___20_11396 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____11402 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____11415  ->
    let uu____11416 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____11416
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____11442  -> let uu____11443 = get_debug ()  in uu____11443 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____11460 = get_debug ()  in
    FStar_All.pipe_right uu____11460
      (FStar_List.existsb (module_name_eq modul))
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____11485 = get_debug ()  in
       FStar_All.pipe_right uu____11485
         (FStar_List.existsb (module_name_eq modul)))
        && (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____11500  ->
    let uu____11501 = get_defensive ()  in uu____11501 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____11511  ->
    let uu____11512 = get_defensive ()  in uu____11512 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11524  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____11531  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____11538  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____11545  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____11555 = get_dump_module ()  in
    FStar_All.pipe_right uu____11555 (FStar_List.existsb (module_name_eq s))
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____11570  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____11577  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____11587 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____11587
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____11623  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____11631  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____11638  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11647  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____11654  -> get_ide () 
let (print : unit -> Prims.bool) = fun uu____11661  -> get_print () 
let (print_in_place : unit -> Prims.bool) =
  fun uu____11668  -> get_print_in_place () 
let profile : 'a . (unit -> 'a) -> ('a -> Prims.string) -> 'a =
  fun f  ->
    fun msg  ->
      let uu____11699 = get_profile ()  in
      if uu____11699
      then
        let uu____11702 = FStar_Util.record_time f  in
        match uu____11702 with
        | (a,time) ->
            ((let uu____11713 = FStar_Util.string_of_int time  in
              let uu____11715 = msg a  in
              FStar_Util.print2 "Elapsed time %s ms: %s\n" uu____11713
                uu____11715);
             a)
      else f ()
  
let (protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____11726  -> get_protect_top_level_axioms () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____11733  ->
    let uu____11734 = get_initial_fuel ()  in
    let uu____11736 = get_max_fuel ()  in Prims.min uu____11734 uu____11736
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____11744  ->
    let uu____11745 = get_initial_ifuel ()  in
    let uu____11747 = get_max_ifuel ()  in Prims.min uu____11745 uu____11747
  
let (interactive : unit -> Prims.bool) =
  fun uu____11755  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____11762  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____11771  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____11778  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____11785  -> get_log_queries () 
let (keep_query_captions : unit -> Prims.bool) =
  fun uu____11792  -> (log_queries ()) && (get_keep_query_captions ()) 
let (log_types : unit -> Prims.bool) = fun uu____11799  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____11806  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____11813  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____11820  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____11827  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____11833  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____11842  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____11849  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____11859 = get_no_extract ()  in
    FStar_All.pipe_right uu____11859 (FStar_List.existsb (module_name_eq s))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____11874  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____11881  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____11888  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____11895  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11904  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____11911  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____11918  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____11925  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____11932  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____11939  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____11946  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____11953  -> get_print_z3_statistics () 
let (query_stats : unit -> Prims.bool) =
  fun uu____11960  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____11967  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11976  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____11983  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____11990  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____11997  ->
    let uu____11998 = get_smtencoding_nl_arith_repr ()  in
    uu____11998 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____12008  ->
    let uu____12009 = get_smtencoding_nl_arith_repr ()  in
    uu____12009 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____12019  ->
    let uu____12020 = get_smtencoding_nl_arith_repr ()  in
    uu____12020 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____12030  ->
    let uu____12031 = get_smtencoding_l_arith_repr ()  in
    uu____12031 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____12041  ->
    let uu____12042 = get_smtencoding_l_arith_repr ()  in
    uu____12042 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____12052  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____12059  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____12066  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____12073  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____12080  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____12087  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____12094  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____12101  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____12108  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____12115  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____12122  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____12129  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____12136  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____12143  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____12152  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____12159  -> get_use_tactics () 
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu____12175  ->
    let uu____12176 = get_using_facts_from ()  in
    match uu____12176 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____12230  ->
    let uu____12231 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____12231
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____12242  ->
    let uu____12243 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____12243 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____12251 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____12262  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____12269  ->
    let uu____12270 = get_smt ()  in
    match uu____12270 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____12288  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____12295  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____12302  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____12309  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____12316  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____12323  ->
    (get_use_two_phase_tc ()) &&
      (let uu____12325 = lax ()  in Prims.op_Negation uu____12325)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____12333  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____12340  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____12347  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____12354  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____12361  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____12378 =
      let uu____12380 = trace_error ()  in Prims.op_Negation uu____12380  in
    if uu____12378
    then
      (push ();
       (let r =
          try
            (fun uu___28_12395  ->
               match () with
               | () -> let uu____12400 = f ()  in FStar_Util.Inr uu____12400)
              ()
          with | uu___27_12402 -> FStar_Util.Inl uu___27_12402  in
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
        | (uu____12483,[]) -> true
        | (m2::ms,p::ps) ->
            (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
        | uu____12516 -> false  in
      let uu____12528 =
        FStar_All.pipe_right setting
          (FStar_Util.try_find
             (fun uu____12570  ->
                match uu____12570 with
                | (path,uu____12581) -> matches_path m_components path))
         in
      match uu____12528 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____12600,flag) -> flag
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____12629 = get_extract ()  in
    match uu____12629 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____12644 =
            let uu____12660 = get_no_extract ()  in
            let uu____12664 = get_extract_namespace ()  in
            let uu____12668 = get_extract_module ()  in
            (uu____12660, uu____12664, uu____12668)  in
          match uu____12644 with
          | ([],[],[]) -> ()
          | uu____12693 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         module_matches_namespace_filter m1 extract_setting)
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____12722 = get_extract_namespace ()  in
          match uu____12722 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____12750 = get_extract_module ()  in
          match uu____12750 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____12772 = no_extract m1  in Prims.op_Negation uu____12772)
          &&
          (let uu____12775 =
             let uu____12786 = get_extract_namespace ()  in
             let uu____12790 = get_extract_module ()  in
             (uu____12786, uu____12790)  in
           (match uu____12775 with
            | ([],[]) -> true
            | uu____12810 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  
let (should_be_already_cached : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____12830 = get_already_cached ()  in
    match uu____12830 with
    | FStar_Pervasives_Native.None  -> false
    | FStar_Pervasives_Native.Some already_cached_setting ->
        module_matches_namespace_filter m already_cached_setting
  
let (error_flags : unit -> error_flag Prims.list) =
  let cache = FStar_Util.smap_create (Prims.parse_int "10")  in
  fun uu____12863  ->
    let we = warn_error ()  in
    let uu____12866 = FStar_Util.smap_try_find cache we  in
    match uu____12866 with
    | FStar_Pervasives_Native.None  ->
        let r = parse_warn_error we  in (FStar_Util.smap_add cache we r; r)
    | FStar_Pervasives_Native.Some r -> r
  