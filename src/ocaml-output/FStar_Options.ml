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
    match projectee with | Low  -> true | uu____34672 -> false
  
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____34683 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | High  -> true | uu____34694 -> false
  
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____34705 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____34718 -> false
  
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
    match projectee with | Bool _0 -> true | uu____34773 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____34797 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____34821 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____34845 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____34870 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____34895 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _34903  -> Bool _34903 
let (mk_string : Prims.string -> option_val) = fun _34910  -> String _34910 
let (mk_path : Prims.string -> option_val) = fun _34917  -> Path _34917 
let (mk_int : Prims.int -> option_val) = fun _34924  -> Int _34924 
let (mk_list : option_val Prims.list -> option_val) =
  fun _34932  -> List _34932 
type options =
  | Set 
  | Reset 
  | Restore 
let (uu___is_Set : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Set  -> true | uu____34942 -> false
  
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____34953 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____34964 -> false
  
type error_flag =
  | CFatal 
  | CAlwaysError 
  | CError 
  | CWarning 
  | CSilent 
let (uu___is_CFatal : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CFatal  -> true | uu____34975 -> false
  
let (uu___is_CAlwaysError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CAlwaysError  -> true | uu____34986 -> false
  
let (uu___is_CError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CError  -> true | uu____34997 -> false
  
let (uu___is_CWarning : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CWarning  -> true | uu____35008 -> false
  
let (uu___is_CSilent : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CSilent  -> true | uu____35019 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____35044  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____35071  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____35099  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___289_35128  ->
    match uu___289_35128 with
    | Bool b -> b
    | uu____35132 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___290_35141  ->
    match uu___290_35141 with
    | Int b -> b
    | uu____35145 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___291_35154  ->
    match uu___291_35154 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____35160 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___292_35170  ->
    match uu___292_35170 with
    | List ts -> ts
    | uu____35176 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____35187 .
    (option_val -> 'Auu____35187) -> option_val -> 'Auu____35187 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____35205 = as_list' x  in
      FStar_All.pipe_right uu____35205 (FStar_List.map as_t)
  
let as_option :
  'Auu____35219 .
    (option_val -> 'Auu____35219) ->
      option_val -> 'Auu____35219 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___293_35234  ->
      match uu___293_35234 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____35238 = as_t v1  in
          FStar_Pervasives_Native.Some uu____35238
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___294_35247  ->
    match uu___294_35247 with
    | List ls ->
        let uu____35254 =
          FStar_List.map
            (fun l  ->
               let uu____35266 = as_string l  in
               FStar_Util.split uu____35266 ",") ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____35254
    | uu____35278 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let copy_optionstate :
  'Auu____35290 .
    'Auu____35290 FStar_Util.smap -> 'Auu____35290 FStar_Util.smap
  = fun m  -> FStar_Util.smap_copy m 
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (internal_peek : unit -> optionstate) =
  fun uu____35331  ->
    let uu____35332 =
      let uu____35335 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____35335  in
    FStar_List.hd uu____35332
  
let (peek : unit -> optionstate) = fun uu____35374  -> internal_peek () 
let (pop : unit -> unit) =
  fun uu____35380  ->
    let uu____35381 = FStar_ST.op_Bang fstar_options  in
    match uu____35381 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____35416::[] -> failwith "TOO MANY POPS!"
    | uu____35424::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____35466  ->
    let uu____35467 =
      let uu____35472 =
        let uu____35475 =
          let uu____35478 = FStar_ST.op_Bang fstar_options  in
          FStar_List.hd uu____35478  in
        FStar_List.map copy_optionstate uu____35475  in
      let uu____35512 = FStar_ST.op_Bang fstar_options  in uu____35472 ::
        uu____35512
       in
    FStar_ST.op_Colon_Equals fstar_options uu____35467
  
let (internal_pop : unit -> Prims.bool) =
  fun uu____35579  ->
    let curstack =
      let uu____35583 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____35583  in
    match curstack with
    | [] -> failwith "impossible: empty current option stack"
    | uu____35620::[] -> false
    | uu____35622::tl1 ->
        ((let uu____35627 =
            let uu____35632 =
              let uu____35637 = FStar_ST.op_Bang fstar_options  in
              FStar_List.tl uu____35637  in
            tl1 :: uu____35632  in
          FStar_ST.op_Colon_Equals fstar_options uu____35627);
         true)
  
let (internal_push : unit -> unit) =
  fun uu____35706  ->
    let curstack =
      let uu____35710 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____35710  in
    let stack' =
      let uu____35747 =
        let uu____35748 = FStar_List.hd curstack  in
        copy_optionstate uu____35748  in
      uu____35747 :: curstack  in
    let uu____35751 =
      let uu____35756 =
        let uu____35761 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____35761  in
      stack' :: uu____35756  in
    FStar_ST.op_Colon_Equals fstar_options uu____35751
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____35830 = FStar_ST.op_Bang fstar_options  in
    match uu____35830 with
    | [] -> failwith "set on empty option stack"
    | []::uu____35865 -> failwith "set on empty current option stack"
    | (uu____35873::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
  
let (snapshot : unit -> (Prims.int * unit)) =
  fun uu____35923  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____35953 = peek ()  in FStar_Util.smap_add uu____35953 k v1
  
let (set_option' : (Prims.string * option_val) -> unit) =
  fun uu____35966  -> match uu____35966 with | (k,v1) -> set_option k v1 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____36005 =
      let uu____36009 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____36009
       in
    FStar_ST.op_Colon_Equals light_off_files uu____36005
  
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
    let uu____36979 = FStar_ST.op_Bang r  in
    match uu____36979 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some f)
    | uu____37114 -> failwith "Multiple initialization of FStar.Options"  in
  let get1 uu____37135 =
    let uu____37136 = FStar_ST.op_Bang r  in
    match uu____37136 with
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
    let uu____37297 = FStar_Pervasives_Native.snd parse_warn_error_set_get ()
       in
    uu____37297 s
  
let (init : unit -> unit) =
  fun uu____37328  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____37348  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____37421 =
      let uu____37424 = peek ()  in FStar_Util.smap_try_find uu____37424 s
       in
    match uu____37421 with
    | FStar_Pervasives_Native.None  ->
        let uu____37427 =
          let uu____37429 = FStar_String.op_Hat s " not found"  in
          FStar_String.op_Hat "Impossible: option " uu____37429  in
        failwith uu____37427
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____37441 .
    Prims.string -> (option_val -> 'Auu____37441) -> 'Auu____37441
  = fun s  -> fun c  -> let uu____37459 = get_option s  in c uu____37459 
let (get_abort_on : unit -> Prims.int) =
  fun uu____37466  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____37475  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____37486  -> lookup_opt "admit_except" (as_option as_string) 
let (get_already_cached :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____37502  ->
    lookup_opt "already_cached" (as_option (as_list as_string))
  
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____37519  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37530  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____37542  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____37551  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37562  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____37576  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____37590  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____37604  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____37615  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37626  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____37638  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____37647  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____37656  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____37667  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____37679  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____37688  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____37701  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____37720  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____37734  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____37746  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____37755  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____37764  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37775  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____37787  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____37796  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____37807  -> lookup_opt "include" (as_list as_string) 
let (get_print : unit -> Prims.bool) =
  fun uu____37819  -> lookup_opt "print" as_bool 
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____37828  -> lookup_opt "print_in_place" as_bool 
let (get_profile : unit -> Prims.bool) =
  fun uu____37837  -> lookup_opt "profile" as_bool 
let (get_protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____37846  -> lookup_opt "protect_top_level_axioms" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____37855  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____37864  -> lookup_opt "initial_ifuel" as_int 
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu____37873  -> lookup_opt "keep_query_captions" as_bool 
let (get_lax : unit -> Prims.bool) =
  fun uu____37882  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____37893  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____37905  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____37914  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____37923  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____37932  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____37941  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____37950  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____37959  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____37968  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____37979  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____37991  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____38000  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____38009  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____38018  ->
    lookup_opt "normalize_pure_terms_for_extraction" as_bool
  
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38029  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____38041  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38052  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____38064  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____38073  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____38082  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____38091  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____38100  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____38109  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____38118  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____38127  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____38136  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38147  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____38159  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38170  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____38182  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____38191  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____38200  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____38209  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____38218  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____38227  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____38236  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____38245  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____38254  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____38263  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____38272  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____38281  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____38290  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____38299  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____38308  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____38317  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____38326  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38337  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____38349  ->
    let uu____38350 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____38350
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____38364  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38383  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____38397  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____38411  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____38423  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____38432  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____38443  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____38455  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____38464  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____38473  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____38482  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____38491  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____38500  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____38509  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____38518  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____38527  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____38536  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___295_38545  ->
    match uu___295_38545 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____38566 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____38575 = get_debug_level ()  in
    FStar_All.pipe_right uu____38575
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "<not set>" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____38741  ->
    let uu____38742 =
      let uu____38744 = FStar_ST.op_Bang _version  in
      let uu____38767 = FStar_ST.op_Bang _platform  in
      let uu____38790 = FStar_ST.op_Bang _compiler  in
      let uu____38813 = FStar_ST.op_Bang _date  in
      let uu____38836 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____38744
        uu____38767 uu____38790 uu____38813 uu____38836
       in
    FStar_Util.print_string uu____38742
  
let display_usage_aux :
  'Auu____38867 'Auu____38868 .
    ('Auu____38867 * Prims.string * 'Auu____38868 FStar_Getopt.opt_variant *
      Prims.string) Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____38923  ->
         match uu____38923 with
         | (uu____38936,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____38955 =
                      let uu____38957 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____38957  in
                    FStar_Util.print_string uu____38955
                  else
                    (let uu____38962 =
                       let uu____38964 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____38964 doc  in
                     FStar_Util.print_string uu____38962)
              | FStar_Getopt.OneArg (uu____38967,argname) ->
                  if doc = ""
                  then
                    let uu____38982 =
                      let uu____38984 = FStar_Util.colorize_bold flag  in
                      let uu____38986 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____38984
                        uu____38986
                       in
                    FStar_Util.print_string uu____38982
                  else
                    (let uu____38991 =
                       let uu____38993 = FStar_Util.colorize_bold flag  in
                       let uu____38995 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____38993
                         uu____38995 doc
                        in
                     FStar_Util.print_string uu____38991))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____39030 = o  in
    match uu____39030 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____39072 =
                let uu____39073 = f ()  in set_option name uu____39073  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____39094 = f x  in set_option name uu____39094
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____39121 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____39121  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____39147 =
        let uu____39150 = lookup_opt name as_list'  in
        FStar_List.append uu____39150 [value]  in
      mk_list uu____39147
  
let accumulate_string :
  'Auu____39164 .
    Prims.string -> ('Auu____39164 -> Prims.string) -> 'Auu____39164 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____39189 =
          let uu____39190 =
            let uu____39191 = post_processor value  in mk_string uu____39191
             in
          accumulated_option name uu____39190  in
        set_option name uu____39189
  
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
    match projectee with | Const _0 -> true | uu____39313 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____39334 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____39356 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____39369 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____39393 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____39419 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____39456 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____39507 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____39548 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____39568 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____39595 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____39639 -> true
    | uu____39642 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____39653 -> uu____39653
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___581_39677  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____39679 ->
                      let uu____39681 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____39681 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____39689 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____39689
                  | PathStr uu____39706 -> mk_path str_val
                  | SimpleStr uu____39708 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____39718 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____39735 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____39735
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
            let uu____39755 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____39755
  
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ  ->
    let desc_of_enum cases =
      let uu____39785 =
        let uu____39787 =
          FStar_String.op_Hat (FStar_String.concat "|" cases) "]"  in
        FStar_String.op_Hat "[" uu____39787  in
      FStar_Pervasives_Native.Some uu____39785  in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____39829,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____39839,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____39870 = desc_of_opt_type typ  in
      match uu____39870 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____39878  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____39904 =
      let uu____39906 = as_string s  in FStar_String.lowercase uu____39906
       in
    mk_string uu____39904
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string)
      Prims.list)
  =
  fun uu____39963  ->
    let uu____39977 =
      let uu____39991 =
        let uu____40005 =
          let uu____40019 =
            let uu____40033 =
              let uu____40045 =
                let uu____40046 = mk_bool true  in Const uu____40046  in
              (FStar_Getopt.noshort, "cache_checked_modules", uu____40045,
                "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
               in
            let uu____40053 =
              let uu____40067 =
                let uu____40081 =
                  let uu____40093 =
                    let uu____40094 = mk_bool true  in Const uu____40094  in
                  (FStar_Getopt.noshort, "cache_off", uu____40093,
                    "Do not read or write any .checked files")
                   in
                let uu____40101 =
                  let uu____40115 =
                    let uu____40127 =
                      let uu____40128 = mk_bool true  in Const uu____40128
                       in
                    (FStar_Getopt.noshort, "cmi", uu____40127,
                      "Inline across module interfaces during extraction (aka. cross-module inlining)")
                     in
                  let uu____40135 =
                    let uu____40149 =
                      let uu____40163 =
                        let uu____40177 =
                          let uu____40191 =
                            let uu____40205 =
                              let uu____40219 =
                                let uu____40233 =
                                  let uu____40245 =
                                    let uu____40246 = mk_bool true  in
                                    Const uu____40246  in
                                  (FStar_Getopt.noshort, "detail_errors",
                                    uu____40245,
                                    "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                   in
                                let uu____40253 =
                                  let uu____40267 =
                                    let uu____40279 =
                                      let uu____40280 = mk_bool true  in
                                      Const uu____40280  in
                                    (FStar_Getopt.noshort,
                                      "detail_hint_replay", uu____40279,
                                      "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                     in
                                  let uu____40287 =
                                    let uu____40301 =
                                      let uu____40313 =
                                        let uu____40314 = mk_bool true  in
                                        Const uu____40314  in
                                      (FStar_Getopt.noshort, "doc",
                                        uu____40313,
                                        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                       in
                                    let uu____40321 =
                                      let uu____40335 =
                                        let uu____40349 =
                                          let uu____40361 =
                                            let uu____40362 = mk_bool true
                                               in
                                            Const uu____40362  in
                                          (FStar_Getopt.noshort,
                                            "eager_inference", uu____40361,
                                            "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                           in
                                        let uu____40369 =
                                          let uu____40383 =
                                            let uu____40395 =
                                              let uu____40396 = mk_bool true
                                                 in
                                              Const uu____40396  in
                                            (FStar_Getopt.noshort,
                                              "eager_subtyping", uu____40395,
                                              "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                             in
                                          let uu____40403 =
                                            let uu____40417 =
                                              let uu____40431 =
                                                let uu____40445 =
                                                  let uu____40459 =
                                                    let uu____40471 =
                                                      let uu____40472 =
                                                        mk_bool true  in
                                                      Const uu____40472  in
                                                    (FStar_Getopt.noshort,
                                                      "expose_interfaces",
                                                      uu____40471,
                                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                     in
                                                  let uu____40479 =
                                                    let uu____40493 =
                                                      let uu____40505 =
                                                        let uu____40506 =
                                                          mk_bool true  in
                                                        Const uu____40506  in
                                                      (FStar_Getopt.noshort,
                                                        "hide_uvar_nums",
                                                        uu____40505,
                                                        "Don't print unification variable numbers")
                                                       in
                                                    let uu____40513 =
                                                      let uu____40527 =
                                                        let uu____40541 =
                                                          let uu____40553 =
                                                            let uu____40554 =
                                                              mk_bool true
                                                               in
                                                            Const uu____40554
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "hint_info",
                                                            uu____40553,
                                                            "Print information regarding hints (deprecated; use --query_stats instead)")
                                                           in
                                                        let uu____40561 =
                                                          let uu____40575 =
                                                            let uu____40587 =
                                                              let uu____40588
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____40588
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "in",
                                                              uu____40587,
                                                              "Legacy interactive mode; reads input from stdin")
                                                             in
                                                          let uu____40595 =
                                                            let uu____40609 =
                                                              let uu____40621
                                                                =
                                                                let uu____40622
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____40622
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "ide",
                                                                uu____40621,
                                                                "JSON-based interactive mode for IDEs")
                                                               in
                                                            let uu____40629 =
                                                              let uu____40643
                                                                =
                                                                let uu____40657
                                                                  =
                                                                  let uu____40669
                                                                    =
                                                                    let uu____40670
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40670
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "print",
                                                                    uu____40669,
                                                                    "Parses and prettyprints the files included on the command line")
                                                                   in
                                                                let uu____40677
                                                                  =
                                                                  let uu____40691
                                                                    =
                                                                    let uu____40703
                                                                    =
                                                                    let uu____40704
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40704
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_in_place",
                                                                    uu____40703,
                                                                    "Parses and prettyprints in place the files included on the command line")
                                                                     in
                                                                  let uu____40711
                                                                    =
                                                                    let uu____40725
                                                                    =
                                                                    let uu____40737
                                                                    =
                                                                    let uu____40738
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40738
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "profile",
                                                                    uu____40737,
                                                                    "Prints timing information for various operations in the compiler")
                                                                     in
                                                                    let uu____40745
                                                                    =
                                                                    let uu____40759
                                                                    =
                                                                    let uu____40773
                                                                    =
                                                                    let uu____40787
                                                                    =
                                                                    let uu____40801
                                                                    =
                                                                    let uu____40815
                                                                    =
                                                                    let uu____40827
                                                                    =
                                                                    let uu____40828
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40828
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____40827,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____40835
                                                                    =
                                                                    let uu____40849
                                                                    =
                                                                    let uu____40863
                                                                    =
                                                                    let uu____40875
                                                                    =
                                                                    let uu____40876
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40876
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____40875,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____40883
                                                                    =
                                                                    let uu____40897
                                                                    =
                                                                    let uu____40909
                                                                    =
                                                                    let uu____40910
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40910
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____40909,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____40917
                                                                    =
                                                                    let uu____40931
                                                                    =
                                                                    let uu____40945
                                                                    =
                                                                    let uu____40959
                                                                    =
                                                                    let uu____40973
                                                                    =
                                                                    let uu____40985
                                                                    =
                                                                    let uu____40986
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40986
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____40985,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____40993
                                                                    =
                                                                    let uu____41007
                                                                    =
                                                                    let uu____41021
                                                                    =
                                                                    let uu____41033
                                                                    =
                                                                    let uu____41034
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41034
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____41033,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____41041
                                                                    =
                                                                    let uu____41055
                                                                    =
                                                                    let uu____41069
                                                                    =
                                                                    let uu____41081
                                                                    =
                                                                    let uu____41082
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41082
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____41081,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____41089
                                                                    =
                                                                    let uu____41103
                                                                    =
                                                                    let uu____41115
                                                                    =
                                                                    let uu____41116
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41116
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____41115,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____41123
                                                                    =
                                                                    let uu____41137
                                                                    =
                                                                    let uu____41149
                                                                    =
                                                                    let uu____41150
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41150
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____41149,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____41157
                                                                    =
                                                                    let uu____41171
                                                                    =
                                                                    let uu____41185
                                                                    =
                                                                    let uu____41199
                                                                    =
                                                                    let uu____41211
                                                                    =
                                                                    let uu____41212
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41212
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____41211,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____41219
                                                                    =
                                                                    let uu____41233
                                                                    =
                                                                    let uu____41245
                                                                    =
                                                                    let uu____41246
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41246
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____41245,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____41253
                                                                    =
                                                                    let uu____41267
                                                                    =
                                                                    let uu____41279
                                                                    =
                                                                    let uu____41280
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41280
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____41279,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____41287
                                                                    =
                                                                    let uu____41301
                                                                    =
                                                                    let uu____41313
                                                                    =
                                                                    let uu____41314
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41314
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____41313,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____41321
                                                                    =
                                                                    let uu____41335
                                                                    =
                                                                    let uu____41347
                                                                    =
                                                                    let uu____41348
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41348
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____41347,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____41355
                                                                    =
                                                                    let uu____41369
                                                                    =
                                                                    let uu____41381
                                                                    =
                                                                    let uu____41382
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41382
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____41381,
                                                                    "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)")
                                                                     in
                                                                    let uu____41389
                                                                    =
                                                                    let uu____41403
                                                                    =
                                                                    let uu____41415
                                                                    =
                                                                    let uu____41416
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41416
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____41415,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____41423
                                                                    =
                                                                    let uu____41437
                                                                    =
                                                                    let uu____41449
                                                                    =
                                                                    let uu____41450
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41450
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____41449,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____41457
                                                                    =
                                                                    let uu____41471
                                                                    =
                                                                    let uu____41483
                                                                    =
                                                                    let uu____41484
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41484
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____41483,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____41491
                                                                    =
                                                                    let uu____41505
                                                                    =
                                                                    let uu____41519
                                                                    =
                                                                    let uu____41531
                                                                    =
                                                                    let uu____41532
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41532
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____41531,
                                                                    "Disable all non-critical output")
                                                                     in
                                                                    let uu____41539
                                                                    =
                                                                    let uu____41553
                                                                    =
                                                                    let uu____41567
                                                                    =
                                                                    let uu____41581
                                                                    =
                                                                    let uu____41595
                                                                    =
                                                                    let uu____41609
                                                                    =
                                                                    let uu____41621
                                                                    =
                                                                    let uu____41622
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41622
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____41621,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____41629
                                                                    =
                                                                    let uu____41643
                                                                    =
                                                                    let uu____41655
                                                                    =
                                                                    let uu____41656
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41656
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____41655,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____41663
                                                                    =
                                                                    let uu____41677
                                                                    =
                                                                    let uu____41689
                                                                    =
                                                                    let uu____41690
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41690
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____41689,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____41697
                                                                    =
                                                                    let uu____41711
                                                                    =
                                                                    let uu____41723
                                                                    =
                                                                    let uu____41724
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41724
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____41723,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____41731
                                                                    =
                                                                    let uu____41745
                                                                    =
                                                                    let uu____41759
                                                                    =
                                                                    let uu____41771
                                                                    =
                                                                    let uu____41772
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41772
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____41771,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____41779
                                                                    =
                                                                    let uu____41793
                                                                    =
                                                                    let uu____41807
                                                                    =
                                                                    let uu____41819
                                                                    =
                                                                    let uu____41820
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41820
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____41819,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____41827
                                                                    =
                                                                    let uu____41841
                                                                    =
                                                                    let uu____41853
                                                                    =
                                                                    let uu____41854
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41854
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____41853,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____41861
                                                                    =
                                                                    let uu____41875
                                                                    =
                                                                    let uu____41887
                                                                    =
                                                                    let uu____41888
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41888
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____41887,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____41895
                                                                    =
                                                                    let uu____41909
                                                                    =
                                                                    let uu____41921
                                                                    =
                                                                    let uu____41922
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41922
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____41921,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____41929
                                                                    =
                                                                    let uu____41943
                                                                    =
                                                                    let uu____41955
                                                                    =
                                                                    let uu____41956
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41956
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____41955,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____41963
                                                                    =
                                                                    let uu____41977
                                                                    =
                                                                    let uu____41989
                                                                    =
                                                                    let uu____41990
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41990
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____41989,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____41997
                                                                    =
                                                                    let uu____42011
                                                                    =
                                                                    let uu____42023
                                                                    =
                                                                    let uu____42024
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42024
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____42023,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____42031
                                                                    =
                                                                    let uu____42045
                                                                    =
                                                                    let uu____42057
                                                                    =
                                                                    let uu____42058
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42058
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____42057,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____42065
                                                                    =
                                                                    let uu____42079
                                                                    =
                                                                    let uu____42093
                                                                    =
                                                                    let uu____42105
                                                                    =
                                                                    let uu____42106
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42106
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____42105,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____42113
                                                                    =
                                                                    let uu____42127
                                                                    =
                                                                    let uu____42139
                                                                    =
                                                                    let uu____42140
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42140
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____42139,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____42147
                                                                    =
                                                                    let uu____42161
                                                                    =
                                                                    let uu____42175
                                                                    =
                                                                    let uu____42189
                                                                    =
                                                                    let uu____42203
                                                                    =
                                                                    let uu____42215
                                                                    =
                                                                    let uu____42216
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42216
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____42215,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____42223
                                                                    =
                                                                    let uu____42237
                                                                    =
                                                                    let uu____42249
                                                                    =
                                                                    let uu____42250
                                                                    =
                                                                    let uu____42258
                                                                    =
                                                                    let uu____42259
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42259
                                                                     in
                                                                    ((fun
                                                                    uu____42266
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____42258)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42250
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____42249,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____42275
                                                                    =
                                                                    let uu____42289
                                                                    =
                                                                    let uu____42301
                                                                    =
                                                                    let uu____42302
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42302
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____42301,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____42309
                                                                    =
                                                                    let uu____42323
                                                                    =
                                                                    let uu____42337
                                                                    =
                                                                    let uu____42349
                                                                    =
                                                                    let uu____42350
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42350
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____42349,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____42357
                                                                    =
                                                                    let uu____42371
                                                                    =
                                                                    let uu____42385
                                                                    =
                                                                    let uu____42399
                                                                    =
                                                                    let uu____42413
                                                                    =
                                                                    let uu____42427
                                                                    =
                                                                    let uu____42439
                                                                    =
                                                                    let uu____42440
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42440
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____42439,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____42447
                                                                    =
                                                                    let uu____42461
                                                                    =
                                                                    let uu____42473
                                                                    =
                                                                    let uu____42474
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42474
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____42473,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____42481
                                                                    =
                                                                    let uu____42495
                                                                    =
                                                                    let uu____42509
                                                                    =
                                                                    let uu____42523
                                                                    =
                                                                    let uu____42537
                                                                    =
                                                                    let uu____42549
                                                                    =
                                                                    let uu____42550
                                                                    =
                                                                    let uu____42558
                                                                    =
                                                                    let uu____42559
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42559
                                                                     in
                                                                    ((fun
                                                                    uu____42565
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____42558)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42550
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____42549,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
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
                                                                    eager_embedding
                                                                    true),
                                                                    uu____42628)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42620
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____42619,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
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
                                                                    uu____42706
                                                                     ->
                                                                    (
                                                                    let uu____42708
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____42708);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____42698)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42690
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____42689,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____42677]
                                                                     in
                                                                    uu____42607
                                                                    ::
                                                                    uu____42663
                                                                     in
                                                                    uu____42537
                                                                    ::
                                                                    uu____42593
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____42523
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____42509
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____42495
                                                                     in
                                                                    uu____42461
                                                                    ::
                                                                    uu____42481
                                                                     in
                                                                    uu____42427
                                                                    ::
                                                                    uu____42447
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____42413
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____42399
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____42385
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____42371
                                                                     in
                                                                    uu____42337
                                                                    ::
                                                                    uu____42357
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____42323
                                                                     in
                                                                    uu____42289
                                                                    ::
                                                                    uu____42309
                                                                     in
                                                                    uu____42237
                                                                    ::
                                                                    uu____42275
                                                                     in
                                                                    uu____42203
                                                                    ::
                                                                    uu____42223
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____42189
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____42175
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____42161
                                                                     in
                                                                    uu____42127
                                                                    ::
                                                                    uu____42147
                                                                     in
                                                                    uu____42093
                                                                    ::
                                                                    uu____42113
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____42079
                                                                     in
                                                                    uu____42045
                                                                    ::
                                                                    uu____42065
                                                                     in
                                                                    uu____42011
                                                                    ::
                                                                    uu____42031
                                                                     in
                                                                    uu____41977
                                                                    ::
                                                                    uu____41997
                                                                     in
                                                                    uu____41943
                                                                    ::
                                                                    uu____41963
                                                                     in
                                                                    uu____41909
                                                                    ::
                                                                    uu____41929
                                                                     in
                                                                    uu____41875
                                                                    ::
                                                                    uu____41895
                                                                     in
                                                                    uu____41841
                                                                    ::
                                                                    uu____41861
                                                                     in
                                                                    uu____41807
                                                                    ::
                                                                    uu____41827
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____41793
                                                                     in
                                                                    uu____41759
                                                                    ::
                                                                    uu____41779
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____41745
                                                                     in
                                                                    uu____41711
                                                                    ::
                                                                    uu____41731
                                                                     in
                                                                    uu____41677
                                                                    ::
                                                                    uu____41697
                                                                     in
                                                                    uu____41643
                                                                    ::
                                                                    uu____41663
                                                                     in
                                                                    uu____41609
                                                                    ::
                                                                    uu____41629
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____41595
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____41581
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____41567
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____41553
                                                                     in
                                                                    uu____41519
                                                                    ::
                                                                    uu____41539
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____41505
                                                                     in
                                                                    uu____41471
                                                                    ::
                                                                    uu____41491
                                                                     in
                                                                    uu____41437
                                                                    ::
                                                                    uu____41457
                                                                     in
                                                                    uu____41403
                                                                    ::
                                                                    uu____41423
                                                                     in
                                                                    uu____41369
                                                                    ::
                                                                    uu____41389
                                                                     in
                                                                    uu____41335
                                                                    ::
                                                                    uu____41355
                                                                     in
                                                                    uu____41301
                                                                    ::
                                                                    uu____41321
                                                                     in
                                                                    uu____41267
                                                                    ::
                                                                    uu____41287
                                                                     in
                                                                    uu____41233
                                                                    ::
                                                                    uu____41253
                                                                     in
                                                                    uu____41199
                                                                    ::
                                                                    uu____41219
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____41185
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____41171
                                                                     in
                                                                    uu____41137
                                                                    ::
                                                                    uu____41157
                                                                     in
                                                                    uu____41103
                                                                    ::
                                                                    uu____41123
                                                                     in
                                                                    uu____41069
                                                                    ::
                                                                    uu____41089
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____41055
                                                                     in
                                                                    uu____41021
                                                                    ::
                                                                    uu____41041
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____41007
                                                                     in
                                                                    uu____40973
                                                                    ::
                                                                    uu____40993
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____40959
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____40945
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____40931
                                                                     in
                                                                    uu____40897
                                                                    ::
                                                                    uu____40917
                                                                     in
                                                                    uu____40863
                                                                    ::
                                                                    uu____40883
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____40849
                                                                     in
                                                                    uu____40815
                                                                    ::
                                                                    uu____40835
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    "Retain comments in the logged SMT queries (requires --log_queries; default true)")
                                                                    ::
                                                                    uu____40801
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____40787
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try initially (default 2)")
                                                                    ::
                                                                    uu____40773
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "protect_top_level_axioms",
                                                                    BoolStr,
                                                                    "Guard nullary top-level symbols in the SMT encoding from provide ambient ground facts (default 'true')")
                                                                    ::
                                                                    uu____40759
                                                                     in
                                                                    uu____40725
                                                                    ::
                                                                    uu____40745
                                                                     in
                                                                  uu____40691
                                                                    ::
                                                                    uu____40711
                                                                   in
                                                                uu____40657
                                                                  ::
                                                                  uu____40677
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "include",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "path")),
                                                                "A directory in which to search for files included on the command line")
                                                                ::
                                                                uu____40643
                                                               in
                                                            uu____40609 ::
                                                              uu____40629
                                                             in
                                                          uu____40575 ::
                                                            uu____40595
                                                           in
                                                        uu____40541 ::
                                                          uu____40561
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "hint_file",
                                                        (PathStr "path"),
                                                        "Read/write hints to <path> (instead of module-specific hints files)")
                                                        :: uu____40527
                                                       in
                                                    uu____40493 ::
                                                      uu____40513
                                                     in
                                                  uu____40459 :: uu____40479
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "extract_namespace",
                                                  (Accumulated
                                                     (PostProcessed
                                                        (pp_lowercase,
                                                          (SimpleStr
                                                             "namespace name")))),
                                                  "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                  :: uu____40445
                                                 in
                                              (FStar_Getopt.noshort,
                                                "extract_module",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "module_name")))),
                                                "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                                :: uu____40431
                                               in
                                            (FStar_Getopt.noshort, "extract",
                                              (Accumulated
                                                 (SimpleStr
                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                              "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                              :: uu____40417
                                             in
                                          uu____40383 :: uu____40403  in
                                        uu____40349 :: uu____40369  in
                                      (FStar_Getopt.noshort, "dump_module",
                                        (Accumulated
                                           (SimpleStr "module_name")), "")
                                        :: uu____40335
                                       in
                                    uu____40301 :: uu____40321  in
                                  uu____40267 :: uu____40287  in
                                uu____40233 :: uu____40253  in
                              (FStar_Getopt.noshort, "dep",
                                (EnumStr ["make"; "graph"; "full"; "raw"]),
                                "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                                :: uu____40219
                               in
                            (FStar_Getopt.noshort, "defensive",
                              (EnumStr ["no"; "warn"; "fail"]),
                              "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                              :: uu____40205
                             in
                          (FStar_Getopt.noshort, "debug_level",
                            (Accumulated
                               (OpenEnumStr
                                  (["Low"; "Medium"; "High"; "Extreme"],
                                    "..."))),
                            "Control the verbosity of debugging info") ::
                            uu____40191
                           in
                        (FStar_Getopt.noshort, "debug",
                          (Accumulated (SimpleStr "module_name")),
                          "Print lots of debugging information while checking module")
                          :: uu____40177
                         in
                      (FStar_Getopt.noshort, "codegen-lib",
                        (Accumulated (SimpleStr "namespace")),
                        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                        :: uu____40163
                       in
                    (FStar_Getopt.noshort, "codegen",
                      (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                      "Generate code for further compilation to executable code, or build a compiler plugin")
                      :: uu____40149
                     in
                  uu____40115 :: uu____40135  in
                uu____40081 :: uu____40101  in
              (FStar_Getopt.noshort, "cache_dir",
                (PostProcessed (pp_validate_dir, (PathStr "dir"))),
                "Read and write .checked and .checked.lax in directory <dir>")
                :: uu____40067
               in
            uu____40033 :: uu____40053  in
          (FStar_Getopt.noshort, "already_cached",
            (Accumulated
               (SimpleStr
                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
            "\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")
            :: uu____40019
           in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____40005
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____39991
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___296_44256  ->
             match uu___296_44256 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____39977

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____44285  ->
    let uu____44288 = specs_with_types ()  in
    FStar_List.map
      (fun uu____44319  ->
         match uu____44319 with
         | (short,long,typ,doc) ->
             let uu____44341 =
               let uu____44355 = arg_spec_of_opt_type long typ  in
               (short, long, uu____44355, doc)  in
             mk_spec uu____44341) uu____44288

let (settable : Prims.string -> Prims.bool) =
  fun uu___297_44370  ->
    match uu___297_44370 with
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
    | uu____44493 -> false
  
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
       (fun uu____44592  ->
          match uu____44592 with
          | (uu____44607,x,uu____44609,uu____44610) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____44685  ->
          match uu____44685 with
          | (uu____44700,x,uu____44702,uu____44703) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____44719  ->
    let uu____44720 = specs ()  in display_usage_aux uu____44720
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____44752 -> true
    | uu____44755 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____44766 -> uu____44766
  
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
        (fun uu___759_44787  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____44804 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____44804
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____44840  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____44846 =
             let uu____44850 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____44850 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____44846)
       in
    let uu____44907 =
      let uu____44911 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____44911
       in
    (res, uu____44907)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____44953  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____44996 = specs ()  in
       FStar_Getopt.parse_cmdline uu____44996 (fun x  -> ())  in
     (let uu____45003 =
        let uu____45009 =
          let uu____45010 = FStar_List.map mk_string old_verify_module  in
          List uu____45010  in
        ("verify_module", uu____45009)  in
      set_option' uu____45003);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____45029 =
        let uu____45031 =
          let uu____45033 =
            let uu____45035 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____45035  in
          (FStar_String.length f1) - uu____45033  in
        uu____45031 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____45029  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____45048 = get_lax ()  in
    if uu____45048
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____45069 = module_name_of_file_name fn  in
    should_verify uu____45069
  
let (module_name_eq : Prims.string -> Prims.string -> Prims.bool) =
  fun m1  ->
    fun m2  -> (FStar_String.lowercase m1) = (FStar_String.lowercase m2)
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____45097 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____45097 (FStar_List.existsb (module_name_eq m))
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____45115 = should_verify m  in
    if uu____45115 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____45132  ->
    let cache_dir =
      let uu____45137 = get_cache_dir ()  in
      match uu____45137 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some c -> [c]  in
    let uu____45151 = get_no_default_includes ()  in
    if uu____45151
    then
      let uu____45157 = get_include ()  in
      FStar_List.append cache_dir uu____45157
    else
      (let lib_paths =
         let uu____45168 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____45168 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = FStar_String.op_Hat fstar_bin_directory "/.."
                in
             let defs = universe_include_path_base_dirs  in
             let uu____45184 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> FStar_String.op_Hat fstar_home x))
                in
             FStar_All.pipe_right uu____45184
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____45211 =
         let uu____45215 =
           let uu____45219 = get_include ()  in
           FStar_List.append uu____45219 ["."]  in
         FStar_List.append lib_paths uu____45215  in
       FStar_List.append cache_dir uu____45211)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____45246 = FStar_Util.smap_try_find file_map filename  in
    match uu____45246 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___810_45268  ->
               match () with
               | () ->
                   let uu____45272 = FStar_Util.is_path_absolute filename  in
                   if uu____45272
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____45288 =
                        let uu____45292 = include_path ()  in
                        FStar_List.rev uu____45292  in
                      FStar_Util.find_map uu____45288
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___809_45320 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____45340  ->
    let uu____45341 = get_prims ()  in
    match uu____45341 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____45350 = find_file filename  in
        (match uu____45350 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____45359 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____45359)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____45372  ->
    let uu____45373 = prims ()  in FStar_Util.basename uu____45373
  
let (pervasives : unit -> Prims.string) =
  fun uu____45381  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____45385 = find_file filename  in
    match uu____45385 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____45394 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____45394
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____45404  ->
    let uu____45405 = pervasives ()  in FStar_Util.basename uu____45405
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____45413  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____45417 = find_file filename  in
    match uu____45417 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____45426 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____45426
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____45439 = get_odir ()  in
    match uu____45439 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____45457 = get_cache_dir ()  in
    match uu____45457 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____45466 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____45466
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns  ->
    let cache = FStar_Util.smap_create (Prims.parse_int "31")  in
    let with_cache f s =
      let uu____45588 = FStar_Util.smap_try_find cache s  in
      match uu____45588 with
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
             let uu____45723 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____45723  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____45746 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              let s1 = FStar_Util.trim_string s  in
              if s1 = ""
              then []
              else
                with_cache
                  (fun s2  ->
                     let uu____45814 =
                       FStar_All.pipe_right (FStar_Util.splitlines s2)
                         (FStar_List.concatMap
                            (fun s3  -> FStar_Util.split s3 " "))
                        in
                     FStar_All.pipe_right uu____45814
                       (FStar_List.map parse_one_setting)) s1))
       in
    FStar_All.pipe_right uu____45746 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____45889 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____45889 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____45904  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____45913  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____45922  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____45929  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____45936  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____45943  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____45953 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____45964 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____45975 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____45986 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____45995  ->
    let uu____45996 = get_codegen ()  in
    FStar_Util.map_opt uu____45996
      (fun uu___298_46002  ->
         match uu___298_46002 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____46008 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____46021  ->
    let uu____46022 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____46022
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____46048  -> let uu____46049 = get_debug ()  in uu____46049 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____46066 = get_debug ()  in
    FStar_All.pipe_right uu____46066
      (FStar_List.existsb (module_name_eq modul))
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____46091 = get_debug ()  in
       FStar_All.pipe_right uu____46091
         (FStar_List.existsb (module_name_eq modul)))
        && (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____46106  ->
    let uu____46107 = get_defensive ()  in uu____46107 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____46117  ->
    let uu____46118 = get_defensive ()  in uu____46118 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46130  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____46137  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____46144  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____46151  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____46161 = get_dump_module ()  in
    FStar_All.pipe_right uu____46161 (FStar_List.existsb (module_name_eq s))
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____46176  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____46183  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____46193 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____46193
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____46229  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____46237  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____46244  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46253  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____46260  -> get_ide () 
let (print : unit -> Prims.bool) = fun uu____46267  -> get_print () 
let (print_in_place : unit -> Prims.bool) =
  fun uu____46274  -> get_print_in_place () 
let profile : 'a . (unit -> 'a) -> ('a -> Prims.string) -> 'a =
  fun f  ->
    fun msg  ->
      let uu____46305 = get_profile ()  in
      if uu____46305
      then
        let uu____46308 = FStar_Util.record_time f  in
        match uu____46308 with
        | (a,time) ->
            ((let uu____46319 = FStar_Util.string_of_int time  in
              let uu____46321 = msg a  in
              FStar_Util.print2 "Elapsed time %s ms: %s\n" uu____46319
                uu____46321);
             a)
      else f ()
  
let (protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____46332  -> get_protect_top_level_axioms () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____46339  ->
    let uu____46340 = get_initial_fuel ()  in
    let uu____46342 = get_max_fuel ()  in Prims.min uu____46340 uu____46342
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____46350  ->
    let uu____46351 = get_initial_ifuel ()  in
    let uu____46353 = get_max_ifuel ()  in Prims.min uu____46351 uu____46353
  
let (interactive : unit -> Prims.bool) =
  fun uu____46361  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____46368  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____46377  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____46384  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____46391  -> get_log_queries () 
let (keep_query_captions : unit -> Prims.bool) =
  fun uu____46398  -> (log_queries ()) && (get_keep_query_captions ()) 
let (log_types : unit -> Prims.bool) = fun uu____46405  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____46412  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____46419  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____46426  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____46433  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____46439  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____46448  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____46455  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____46465 = get_no_extract ()  in
    FStar_All.pipe_right uu____46465 (FStar_List.existsb (module_name_eq s))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____46480  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____46487  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____46494  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____46501  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46510  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____46517  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____46524  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____46531  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____46538  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____46545  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____46552  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____46559  -> get_print_z3_statistics () 
let (query_stats : unit -> Prims.bool) =
  fun uu____46566  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____46573  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46582  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____46589  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____46596  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____46603  ->
    let uu____46604 = get_smtencoding_nl_arith_repr ()  in
    uu____46604 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____46614  ->
    let uu____46615 = get_smtencoding_nl_arith_repr ()  in
    uu____46615 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____46625  ->
    let uu____46626 = get_smtencoding_nl_arith_repr ()  in
    uu____46626 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____46636  ->
    let uu____46637 = get_smtencoding_l_arith_repr ()  in
    uu____46637 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____46647  ->
    let uu____46648 = get_smtencoding_l_arith_repr ()  in
    uu____46648 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____46658  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____46665  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____46672  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____46679  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____46686  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____46693  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____46700  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____46707  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____46714  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____46721  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____46728  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____46735  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____46742  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____46749  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46758  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____46765  -> get_use_tactics () 
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu____46781  ->
    let uu____46782 = get_using_facts_from ()  in
    match uu____46782 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____46836  ->
    let uu____46837 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____46837
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____46848  ->
    let uu____46849 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____46849 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____46857 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____46868  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____46875  ->
    let uu____46876 = get_smt ()  in
    match uu____46876 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____46894  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____46901  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____46908  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____46915  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____46922  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____46929  ->
    (get_use_two_phase_tc ()) &&
      (let uu____46931 = lax ()  in Prims.op_Negation uu____46931)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____46939  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____46946  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____46953  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____46960  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____46967  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____46984 =
      let uu____46986 = trace_error ()  in Prims.op_Negation uu____46986  in
    if uu____46984
    then
      (push ();
       (let r =
          try
            (fun uu___1009_47001  ->
               match () with
               | () -> let uu____47006 = f ()  in FStar_Util.Inr uu____47006)
              ()
          with | uu___1008_47008 -> FStar_Util.Inl uu___1008_47008  in
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
        | (uu____47089,[]) -> true
        | (m2::ms,p::ps) ->
            (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
        | uu____47122 -> false  in
      let uu____47134 =
        FStar_All.pipe_right setting
          (FStar_Util.try_find
             (fun uu____47176  ->
                match uu____47176 with
                | (path,uu____47187) -> matches_path m_components path))
         in
      match uu____47134 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____47206,flag) -> flag
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____47235 = get_extract ()  in
    match uu____47235 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____47250 =
            let uu____47266 = get_no_extract ()  in
            let uu____47270 = get_extract_namespace ()  in
            let uu____47274 = get_extract_module ()  in
            (uu____47266, uu____47270, uu____47274)  in
          match uu____47250 with
          | ([],[],[]) -> ()
          | uu____47299 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         module_matches_namespace_filter m1 extract_setting)
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____47328 = get_extract_namespace ()  in
          match uu____47328 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____47356 = get_extract_module ()  in
          match uu____47356 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____47378 = no_extract m1  in Prims.op_Negation uu____47378)
          &&
          (let uu____47381 =
             let uu____47392 = get_extract_namespace ()  in
             let uu____47396 = get_extract_module ()  in
             (uu____47392, uu____47396)  in
           (match uu____47381 with
            | ([],[]) -> true
            | uu____47416 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  
let (should_be_already_cached : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____47436 = get_already_cached ()  in
    match uu____47436 with
    | FStar_Pervasives_Native.None  -> false
    | FStar_Pervasives_Native.Some already_cached_setting ->
        module_matches_namespace_filter m already_cached_setting
  
let (error_flags : unit -> error_flag Prims.list) =
  let cache = FStar_Util.smap_create (Prims.parse_int "10")  in
  fun uu____47469  ->
    let we = warn_error ()  in
    let uu____47472 = FStar_Util.smap_try_find cache we  in
    match uu____47472 with
    | FStar_Pervasives_Native.None  ->
        let r = parse_warn_error we  in (FStar_Util.smap_add cache we r; r)
    | FStar_Pervasives_Native.Some r -> r
  