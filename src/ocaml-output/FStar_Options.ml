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
    match projectee with | Low  -> true | uu____30533 -> false
  
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____30544 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | High  -> true | uu____30555 -> false
  
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____30566 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____30579 -> false
  
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
    match projectee with | Bool _0 -> true | uu____30633 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____30656 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____30679 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____30702 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____30726 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____30750 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _30758  -> Bool _30758 
let (mk_string : Prims.string -> option_val) = fun _30765  -> String _30765 
let (mk_path : Prims.string -> option_val) = fun _30772  -> Path _30772 
let (mk_int : Prims.int -> option_val) = fun _30779  -> Int _30779 
let (mk_list : option_val Prims.list -> option_val) =
  fun _30787  -> List _30787 
type options =
  | Set 
  | Reset 
  | Restore 
let (uu___is_Set : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Set  -> true | uu____30797 -> false
  
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____30808 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____30819 -> false
  
type error_flag =
  | CFatal 
  | CAlwaysError 
  | CError 
  | CWarning 
  | CSilent 
let (uu___is_CFatal : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CFatal  -> true | uu____30830 -> false
  
let (uu___is_CAlwaysError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CAlwaysError  -> true | uu____30841 -> false
  
let (uu___is_CError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CError  -> true | uu____30852 -> false
  
let (uu___is_CWarning : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CWarning  -> true | uu____30863 -> false
  
let (uu___is_CSilent : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CSilent  -> true | uu____30874 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____30888  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____30915  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____30943  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___289_30972  ->
    match uu___289_30972 with
    | Bool b -> b
    | uu____30976 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___290_30985  ->
    match uu___290_30985 with
    | Int b -> b
    | uu____30989 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___291_30998  ->
    match uu___291_30998 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____31004 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___292_31014  ->
    match uu___292_31014 with
    | List ts -> ts
    | uu____31020 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____31031 .
    (option_val -> 'Auu____31031) -> option_val -> 'Auu____31031 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____31049 = as_list' x  in
      FStar_All.pipe_right uu____31049 (FStar_List.map as_t)
  
let as_option :
  'Auu____31063 .
    (option_val -> 'Auu____31063) ->
      option_val -> 'Auu____31063 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___293_31078  ->
      match uu___293_31078 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____31082 = as_t v1  in
          FStar_Pervasives_Native.Some uu____31082
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___294_31091  ->
    match uu___294_31091 with
    | List ls ->
        let uu____31098 =
          FStar_List.map
            (fun l  ->
               let uu____31110 = as_string l  in
               FStar_Util.split uu____31110 ",") ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____31098
    | uu____31122 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let copy_optionstate :
  'Auu____31134 .
    'Auu____31134 FStar_Util.smap -> 'Auu____31134 FStar_Util.smap
  = fun m  -> FStar_Util.smap_copy m 
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (internal_peek : unit -> optionstate) =
  fun uu____31164  ->
    let uu____31165 =
      let uu____31168 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____31168  in
    FStar_List.hd uu____31165
  
let (peek : unit -> optionstate) = fun uu____31207  -> internal_peek () 
let (pop : unit -> unit) =
  fun uu____31213  ->
    let uu____31214 = FStar_ST.op_Bang fstar_options  in
    match uu____31214 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____31249::[] -> failwith "TOO MANY POPS!"
    | uu____31257::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____31299  ->
    let uu____31300 =
      let uu____31305 =
        let uu____31308 =
          let uu____31311 = FStar_ST.op_Bang fstar_options  in
          FStar_List.hd uu____31311  in
        FStar_List.map copy_optionstate uu____31308  in
      let uu____31345 = FStar_ST.op_Bang fstar_options  in uu____31305 ::
        uu____31345
       in
    FStar_ST.op_Colon_Equals fstar_options uu____31300
  
let (internal_pop : unit -> Prims.bool) =
  fun uu____31412  ->
    let curstack =
      let uu____31416 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____31416  in
    match curstack with
    | [] -> failwith "impossible: empty current option stack"
    | uu____31453::[] -> false
    | uu____31455::tl1 ->
        ((let uu____31460 =
            let uu____31465 =
              let uu____31470 = FStar_ST.op_Bang fstar_options  in
              FStar_List.tl uu____31470  in
            tl1 :: uu____31465  in
          FStar_ST.op_Colon_Equals fstar_options uu____31460);
         true)
  
let (internal_push : unit -> unit) =
  fun uu____31539  ->
    let curstack =
      let uu____31543 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____31543  in
    let stack' =
      let uu____31580 =
        let uu____31581 = FStar_List.hd curstack  in
        copy_optionstate uu____31581  in
      uu____31580 :: curstack  in
    let uu____31584 =
      let uu____31589 =
        let uu____31594 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____31594  in
      stack' :: uu____31589  in
    FStar_ST.op_Colon_Equals fstar_options uu____31584
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____31663 = FStar_ST.op_Bang fstar_options  in
    match uu____31663 with
    | [] -> failwith "set on empty option stack"
    | []::uu____31698 -> failwith "set on empty current option stack"
    | (uu____31706::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
  
let (snapshot : unit -> (Prims.int * unit)) =
  fun uu____31756  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____31786 = peek ()  in FStar_Util.smap_add uu____31786 k v1
  
let (set_option' : (Prims.string * option_val) -> unit) =
  fun uu____31799  -> match uu____31799 with | (k,v1) -> set_option k v1 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____31827 =
      let uu____31831 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____31831
       in
    FStar_ST.op_Colon_Equals light_off_files uu____31827
  
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
    let uu____32801 = FStar_ST.op_Bang r  in
    match uu____32801 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some f)
    | uu____32892 -> failwith "Multiple initialization of FStar.Options"  in
  let get1 uu____32913 =
    let uu____32914 = FStar_ST.op_Bang r  in
    match uu____32914 with
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
    let uu____33053 = FStar_Pervasives_Native.snd parse_warn_error_set_get ()
       in
    uu____33053 s
  
let (init : unit -> unit) =
  fun uu____33084  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____33104  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____33177 =
      let uu____33180 = peek ()  in FStar_Util.smap_try_find uu____33180 s
       in
    match uu____33177 with
    | FStar_Pervasives_Native.None  ->
        let uu____33183 =
          let uu____33185 = FStar_String.op_Hat s " not found"  in
          FStar_String.op_Hat "Impossible: option " uu____33185  in
        failwith uu____33183
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____33197 .
    Prims.string -> (option_val -> 'Auu____33197) -> 'Auu____33197
  = fun s  -> fun c  -> let uu____33215 = get_option s  in c uu____33215 
let (get_abort_on : unit -> Prims.int) =
  fun uu____33222  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____33231  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____33242  -> lookup_opt "admit_except" (as_option as_string) 
let (get_already_cached :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____33258  ->
    lookup_opt "already_cached" (as_option (as_list as_string))
  
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____33275  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33286  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____33298  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____33307  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33318  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____33332  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____33346  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____33360  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____33371  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33382  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____33394  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____33403  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____33412  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____33423  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____33435  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____33444  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____33457  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____33476  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____33490  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____33502  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____33511  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____33520  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33531  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____33543  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____33552  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____33563  -> lookup_opt "include" (as_list as_string) 
let (get_print : unit -> Prims.bool) =
  fun uu____33575  -> lookup_opt "print" as_bool 
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____33584  -> lookup_opt "print_in_place" as_bool 
let (get_profile : unit -> Prims.bool) =
  fun uu____33593  -> lookup_opt "profile" as_bool 
let (get_protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____33602  -> lookup_opt "protect_top_level_axioms" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____33611  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____33620  -> lookup_opt "initial_ifuel" as_int 
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu____33629  -> lookup_opt "keep_query_captions" as_bool 
let (get_lax : unit -> Prims.bool) =
  fun uu____33638  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____33649  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____33661  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____33670  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____33679  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____33688  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____33697  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____33706  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____33715  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____33724  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____33735  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____33747  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____33756  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____33765  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____33774  ->
    lookup_opt "normalize_pure_terms_for_extraction" as_bool
  
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33785  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____33797  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33808  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____33820  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____33829  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____33838  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____33847  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____33856  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____33865  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____33874  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____33883  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____33892  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33903  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____33915  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33926  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____33938  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____33947  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____33956  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____33965  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____33974  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____33983  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____33992  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____34001  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____34010  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____34019  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____34028  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____34037  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____34046  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____34055  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____34064  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____34073  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____34082  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____34093  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____34105  ->
    let uu____34106 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____34106
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____34120  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____34139  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____34153  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____34167  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____34179  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____34188  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____34199  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____34211  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____34220  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____34229  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____34238  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____34247  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____34256  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____34265  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____34274  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____34283  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____34292  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___295_34301  ->
    match uu___295_34301 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____34322 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____34331 = get_debug_level ()  in
    FStar_All.pipe_right uu____34331
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "<not set>" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____34387  ->
    let uu____34388 =
      let uu____34390 = FStar_ST.op_Bang _version  in
      let uu____34413 = FStar_ST.op_Bang _platform  in
      let uu____34436 = FStar_ST.op_Bang _compiler  in
      let uu____34459 = FStar_ST.op_Bang _date  in
      let uu____34482 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____34390
        uu____34413 uu____34436 uu____34459 uu____34482
       in
    FStar_Util.print_string uu____34388
  
let display_usage_aux :
  'Auu____34513 'Auu____34514 .
    ('Auu____34513 * Prims.string * 'Auu____34514 FStar_Getopt.opt_variant *
      Prims.string) Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____34569  ->
         match uu____34569 with
         | (uu____34582,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____34601 =
                      let uu____34603 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____34603  in
                    FStar_Util.print_string uu____34601
                  else
                    (let uu____34608 =
                       let uu____34610 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____34610 doc  in
                     FStar_Util.print_string uu____34608)
              | FStar_Getopt.OneArg (uu____34613,argname) ->
                  if doc = ""
                  then
                    let uu____34628 =
                      let uu____34630 = FStar_Util.colorize_bold flag  in
                      let uu____34632 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____34630
                        uu____34632
                       in
                    FStar_Util.print_string uu____34628
                  else
                    (let uu____34637 =
                       let uu____34639 = FStar_Util.colorize_bold flag  in
                       let uu____34641 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____34639
                         uu____34641 doc
                        in
                     FStar_Util.print_string uu____34637))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____34676 = o  in
    match uu____34676 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____34718 =
                let uu____34719 = f ()  in set_option name uu____34719  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____34740 = f x  in set_option name uu____34740
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____34767 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____34767  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____34793 =
        let uu____34796 = lookup_opt name as_list'  in
        FStar_List.append uu____34796 [value]  in
      mk_list uu____34793
  
let accumulate_string :
  'Auu____34810 .
    Prims.string -> ('Auu____34810 -> Prims.string) -> 'Auu____34810 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____34835 =
          let uu____34836 =
            let uu____34837 = post_processor value  in mk_string uu____34837
             in
          accumulated_option name uu____34836  in
        set_option name uu____34835
  
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
    match projectee with | Const _0 -> true | uu____34959 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____34979 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____35000 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____35013 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____35036 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____35061 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____35097 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____35147 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____35187 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____35206 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____35232 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____35275 -> true
    | uu____35278 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____35288 -> uu____35288
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___581_35312  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____35314 ->
                      let uu____35316 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____35316 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____35324 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____35324
                  | PathStr uu____35341 -> mk_path str_val
                  | SimpleStr uu____35343 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____35353 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____35370 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____35370
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
            let uu____35390 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____35390
  
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ  ->
    let desc_of_enum cases =
      let uu____35420 =
        let uu____35422 =
          FStar_String.op_Hat (FStar_String.concat "|" cases) "]"  in
        FStar_String.op_Hat "[" uu____35422  in
      FStar_Pervasives_Native.Some uu____35420  in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____35464,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____35474,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____35505 = desc_of_opt_type typ  in
      match uu____35505 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____35513  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____35539 =
      let uu____35541 = as_string s  in FStar_String.lowercase uu____35541
       in
    mk_string uu____35539
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string)
      Prims.list)
  =
  fun uu____35576  ->
    let uu____35590 =
      let uu____35604 =
        let uu____35618 =
          let uu____35632 =
            let uu____35646 =
              let uu____35658 =
                let uu____35659 = mk_bool true  in Const uu____35659  in
              (FStar_Getopt.noshort, "cache_checked_modules", uu____35658,
                "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
               in
            let uu____35666 =
              let uu____35680 =
                let uu____35694 =
                  let uu____35706 =
                    let uu____35707 = mk_bool true  in Const uu____35707  in
                  (FStar_Getopt.noshort, "cache_off", uu____35706,
                    "Do not read or write any .checked files")
                   in
                let uu____35714 =
                  let uu____35728 =
                    let uu____35740 =
                      let uu____35741 = mk_bool true  in Const uu____35741
                       in
                    (FStar_Getopt.noshort, "cmi", uu____35740,
                      "Inline across module interfaces during extraction (aka. cross-module inlining)")
                     in
                  let uu____35748 =
                    let uu____35762 =
                      let uu____35776 =
                        let uu____35790 =
                          let uu____35804 =
                            let uu____35818 =
                              let uu____35832 =
                                let uu____35846 =
                                  let uu____35858 =
                                    let uu____35859 = mk_bool true  in
                                    Const uu____35859  in
                                  (FStar_Getopt.noshort, "detail_errors",
                                    uu____35858,
                                    "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                   in
                                let uu____35866 =
                                  let uu____35880 =
                                    let uu____35892 =
                                      let uu____35893 = mk_bool true  in
                                      Const uu____35893  in
                                    (FStar_Getopt.noshort,
                                      "detail_hint_replay", uu____35892,
                                      "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                     in
                                  let uu____35900 =
                                    let uu____35914 =
                                      let uu____35926 =
                                        let uu____35927 = mk_bool true  in
                                        Const uu____35927  in
                                      (FStar_Getopt.noshort, "doc",
                                        uu____35926,
                                        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                       in
                                    let uu____35934 =
                                      let uu____35948 =
                                        let uu____35962 =
                                          let uu____35974 =
                                            let uu____35975 = mk_bool true
                                               in
                                            Const uu____35975  in
                                          (FStar_Getopt.noshort,
                                            "eager_inference", uu____35974,
                                            "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                           in
                                        let uu____35982 =
                                          let uu____35996 =
                                            let uu____36008 =
                                              let uu____36009 = mk_bool true
                                                 in
                                              Const uu____36009  in
                                            (FStar_Getopt.noshort,
                                              "eager_subtyping", uu____36008,
                                              "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                             in
                                          let uu____36016 =
                                            let uu____36030 =
                                              let uu____36044 =
                                                let uu____36058 =
                                                  let uu____36072 =
                                                    let uu____36084 =
                                                      let uu____36085 =
                                                        mk_bool true  in
                                                      Const uu____36085  in
                                                    (FStar_Getopt.noshort,
                                                      "expose_interfaces",
                                                      uu____36084,
                                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                     in
                                                  let uu____36092 =
                                                    let uu____36106 =
                                                      let uu____36118 =
                                                        let uu____36119 =
                                                          mk_bool true  in
                                                        Const uu____36119  in
                                                      (FStar_Getopt.noshort,
                                                        "hide_uvar_nums",
                                                        uu____36118,
                                                        "Don't print unification variable numbers")
                                                       in
                                                    let uu____36126 =
                                                      let uu____36140 =
                                                        let uu____36154 =
                                                          let uu____36166 =
                                                            let uu____36167 =
                                                              mk_bool true
                                                               in
                                                            Const uu____36167
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "hint_info",
                                                            uu____36166,
                                                            "Print information regarding hints (deprecated; use --query_stats instead)")
                                                           in
                                                        let uu____36174 =
                                                          let uu____36188 =
                                                            let uu____36200 =
                                                              let uu____36201
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____36201
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "in",
                                                              uu____36200,
                                                              "Legacy interactive mode; reads input from stdin")
                                                             in
                                                          let uu____36208 =
                                                            let uu____36222 =
                                                              let uu____36234
                                                                =
                                                                let uu____36235
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____36235
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "ide",
                                                                uu____36234,
                                                                "JSON-based interactive mode for IDEs")
                                                               in
                                                            let uu____36242 =
                                                              let uu____36256
                                                                =
                                                                let uu____36270
                                                                  =
                                                                  let uu____36282
                                                                    =
                                                                    let uu____36283
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36283
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "print",
                                                                    uu____36282,
                                                                    "Parses and prettyprints the files included on the command line")
                                                                   in
                                                                let uu____36290
                                                                  =
                                                                  let uu____36304
                                                                    =
                                                                    let uu____36316
                                                                    =
                                                                    let uu____36317
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36317
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_in_place",
                                                                    uu____36316,
                                                                    "Parses and prettyprints in place the files included on the command line")
                                                                     in
                                                                  let uu____36324
                                                                    =
                                                                    let uu____36338
                                                                    =
                                                                    let uu____36350
                                                                    =
                                                                    let uu____36351
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36351
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "profile",
                                                                    uu____36350,
                                                                    "Prints timing information for various operations in the compiler")
                                                                     in
                                                                    let uu____36358
                                                                    =
                                                                    let uu____36372
                                                                    =
                                                                    let uu____36386
                                                                    =
                                                                    let uu____36400
                                                                    =
                                                                    let uu____36414
                                                                    =
                                                                    let uu____36428
                                                                    =
                                                                    let uu____36440
                                                                    =
                                                                    let uu____36441
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36441
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____36440,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____36448
                                                                    =
                                                                    let uu____36462
                                                                    =
                                                                    let uu____36476
                                                                    =
                                                                    let uu____36488
                                                                    =
                                                                    let uu____36489
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36489
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____36488,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____36496
                                                                    =
                                                                    let uu____36510
                                                                    =
                                                                    let uu____36522
                                                                    =
                                                                    let uu____36523
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36523
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____36522,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____36530
                                                                    =
                                                                    let uu____36544
                                                                    =
                                                                    let uu____36558
                                                                    =
                                                                    let uu____36572
                                                                    =
                                                                    let uu____36586
                                                                    =
                                                                    let uu____36598
                                                                    =
                                                                    let uu____36599
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36599
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____36598,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____36606
                                                                    =
                                                                    let uu____36620
                                                                    =
                                                                    let uu____36634
                                                                    =
                                                                    let uu____36646
                                                                    =
                                                                    let uu____36647
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36647
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____36646,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____36654
                                                                    =
                                                                    let uu____36668
                                                                    =
                                                                    let uu____36682
                                                                    =
                                                                    let uu____36694
                                                                    =
                                                                    let uu____36695
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36695
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____36694,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____36702
                                                                    =
                                                                    let uu____36716
                                                                    =
                                                                    let uu____36728
                                                                    =
                                                                    let uu____36729
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36729
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____36728,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____36736
                                                                    =
                                                                    let uu____36750
                                                                    =
                                                                    let uu____36762
                                                                    =
                                                                    let uu____36763
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36763
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____36762,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____36770
                                                                    =
                                                                    let uu____36784
                                                                    =
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
                                                                    "print_bound_var_types",
                                                                    uu____36824,
                                                                    "Print the types of bound variables")
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
                                                                    "print_effect_args",
                                                                    uu____36858,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____36866
                                                                    =
                                                                    let uu____36880
                                                                    =
                                                                    let uu____36892
                                                                    =
                                                                    let uu____36893
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36893
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____36892,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____36900
                                                                    =
                                                                    let uu____36914
                                                                    =
                                                                    let uu____36926
                                                                    =
                                                                    let uu____36927
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36927
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____36926,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____36934
                                                                    =
                                                                    let uu____36948
                                                                    =
                                                                    let uu____36960
                                                                    =
                                                                    let uu____36961
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36961
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____36960,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____36968
                                                                    =
                                                                    let uu____36982
                                                                    =
                                                                    let uu____36994
                                                                    =
                                                                    let uu____36995
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36995
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____36994,
                                                                    "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)")
                                                                     in
                                                                    let uu____37002
                                                                    =
                                                                    let uu____37016
                                                                    =
                                                                    let uu____37028
                                                                    =
                                                                    let uu____37029
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37029
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____37028,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____37036
                                                                    =
                                                                    let uu____37050
                                                                    =
                                                                    let uu____37062
                                                                    =
                                                                    let uu____37063
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37063
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____37062,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____37070
                                                                    =
                                                                    let uu____37084
                                                                    =
                                                                    let uu____37096
                                                                    =
                                                                    let uu____37097
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37097
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____37096,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____37104
                                                                    =
                                                                    let uu____37118
                                                                    =
                                                                    let uu____37132
                                                                    =
                                                                    let uu____37144
                                                                    =
                                                                    let uu____37145
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37145
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____37144,
                                                                    "Disable all non-critical output")
                                                                     in
                                                                    let uu____37152
                                                                    =
                                                                    let uu____37166
                                                                    =
                                                                    let uu____37180
                                                                    =
                                                                    let uu____37194
                                                                    =
                                                                    let uu____37208
                                                                    =
                                                                    let uu____37222
                                                                    =
                                                                    let uu____37234
                                                                    =
                                                                    let uu____37235
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37235
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____37234,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____37242
                                                                    =
                                                                    let uu____37256
                                                                    =
                                                                    let uu____37268
                                                                    =
                                                                    let uu____37269
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37269
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____37268,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____37276
                                                                    =
                                                                    let uu____37290
                                                                    =
                                                                    let uu____37302
                                                                    =
                                                                    let uu____37303
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37303
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____37302,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____37310
                                                                    =
                                                                    let uu____37324
                                                                    =
                                                                    let uu____37336
                                                                    =
                                                                    let uu____37337
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37337
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____37336,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____37344
                                                                    =
                                                                    let uu____37358
                                                                    =
                                                                    let uu____37372
                                                                    =
                                                                    let uu____37384
                                                                    =
                                                                    let uu____37385
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37385
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____37384,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____37392
                                                                    =
                                                                    let uu____37406
                                                                    =
                                                                    let uu____37420
                                                                    =
                                                                    let uu____37432
                                                                    =
                                                                    let uu____37433
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37433
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____37432,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____37440
                                                                    =
                                                                    let uu____37454
                                                                    =
                                                                    let uu____37466
                                                                    =
                                                                    let uu____37467
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37467
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____37466,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____37474
                                                                    =
                                                                    let uu____37488
                                                                    =
                                                                    let uu____37500
                                                                    =
                                                                    let uu____37501
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37501
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____37500,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____37508
                                                                    =
                                                                    let uu____37522
                                                                    =
                                                                    let uu____37534
                                                                    =
                                                                    let uu____37535
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37535
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____37534,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____37542
                                                                    =
                                                                    let uu____37556
                                                                    =
                                                                    let uu____37568
                                                                    =
                                                                    let uu____37569
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37569
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____37568,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____37576
                                                                    =
                                                                    let uu____37590
                                                                    =
                                                                    let uu____37602
                                                                    =
                                                                    let uu____37603
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37603
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____37602,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____37610
                                                                    =
                                                                    let uu____37624
                                                                    =
                                                                    let uu____37636
                                                                    =
                                                                    let uu____37637
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37637
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____37636,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____37644
                                                                    =
                                                                    let uu____37658
                                                                    =
                                                                    let uu____37670
                                                                    =
                                                                    let uu____37671
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37671
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____37670,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____37678
                                                                    =
                                                                    let uu____37692
                                                                    =
                                                                    let uu____37706
                                                                    =
                                                                    let uu____37718
                                                                    =
                                                                    let uu____37719
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37719
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____37718,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____37726
                                                                    =
                                                                    let uu____37740
                                                                    =
                                                                    let uu____37752
                                                                    =
                                                                    let uu____37753
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37753
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____37752,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____37760
                                                                    =
                                                                    let uu____37774
                                                                    =
                                                                    let uu____37788
                                                                    =
                                                                    let uu____37802
                                                                    =
                                                                    let uu____37816
                                                                    =
                                                                    let uu____37828
                                                                    =
                                                                    let uu____37829
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37829
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____37828,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____37836
                                                                    =
                                                                    let uu____37850
                                                                    =
                                                                    let uu____37862
                                                                    =
                                                                    let uu____37863
                                                                    =
                                                                    let uu____37871
                                                                    =
                                                                    let uu____37872
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37872
                                                                     in
                                                                    ((fun
                                                                    uu____37879
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____37871)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____37863
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____37862,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____37888
                                                                    =
                                                                    let uu____37902
                                                                    =
                                                                    let uu____37914
                                                                    =
                                                                    let uu____37915
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37915
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____37914,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____37922
                                                                    =
                                                                    let uu____37936
                                                                    =
                                                                    let uu____37950
                                                                    =
                                                                    let uu____37962
                                                                    =
                                                                    let uu____37963
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37963
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____37962,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____37970
                                                                    =
                                                                    let uu____37984
                                                                    =
                                                                    let uu____37998
                                                                    =
                                                                    let uu____38012
                                                                    =
                                                                    let uu____38026
                                                                    =
                                                                    let uu____38040
                                                                    =
                                                                    let uu____38052
                                                                    =
                                                                    let uu____38053
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38053
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____38052,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____38060
                                                                    =
                                                                    let uu____38074
                                                                    =
                                                                    let uu____38086
                                                                    =
                                                                    let uu____38087
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38087
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____38086,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____38094
                                                                    =
                                                                    let uu____38108
                                                                    =
                                                                    let uu____38122
                                                                    =
                                                                    let uu____38136
                                                                    =
                                                                    let uu____38150
                                                                    =
                                                                    let uu____38162
                                                                    =
                                                                    let uu____38163
                                                                    =
                                                                    let uu____38171
                                                                    =
                                                                    let uu____38172
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38172
                                                                     in
                                                                    ((fun
                                                                    uu____38178
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____38171)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____38163
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____38162,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____38206
                                                                    =
                                                                    let uu____38220
                                                                    =
                                                                    let uu____38232
                                                                    =
                                                                    let uu____38233
                                                                    =
                                                                    let uu____38241
                                                                    =
                                                                    let uu____38242
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38242
                                                                     in
                                                                    ((fun
                                                                    uu____38248
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____38241)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____38233
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____38232,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____38276
                                                                    =
                                                                    let uu____38290
                                                                    =
                                                                    let uu____38302
                                                                    =
                                                                    let uu____38303
                                                                    =
                                                                    let uu____38311
                                                                    =
                                                                    let uu____38312
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38312
                                                                     in
                                                                    ((fun
                                                                    uu____38319
                                                                     ->
                                                                    (
                                                                    let uu____38321
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____38321);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____38311)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____38303
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____38302,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____38290]
                                                                     in
                                                                    uu____38220
                                                                    ::
                                                                    uu____38276
                                                                     in
                                                                    uu____38150
                                                                    ::
                                                                    uu____38206
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____38136
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____38122
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____38108
                                                                     in
                                                                    uu____38074
                                                                    ::
                                                                    uu____38094
                                                                     in
                                                                    uu____38040
                                                                    ::
                                                                    uu____38060
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____38026
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____38012
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____37998
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____37984
                                                                     in
                                                                    uu____37950
                                                                    ::
                                                                    uu____37970
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____37936
                                                                     in
                                                                    uu____37902
                                                                    ::
                                                                    uu____37922
                                                                     in
                                                                    uu____37850
                                                                    ::
                                                                    uu____37888
                                                                     in
                                                                    uu____37816
                                                                    ::
                                                                    uu____37836
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____37802
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____37788
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____37774
                                                                     in
                                                                    uu____37740
                                                                    ::
                                                                    uu____37760
                                                                     in
                                                                    uu____37706
                                                                    ::
                                                                    uu____37726
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____37692
                                                                     in
                                                                    uu____37658
                                                                    ::
                                                                    uu____37678
                                                                     in
                                                                    uu____37624
                                                                    ::
                                                                    uu____37644
                                                                     in
                                                                    uu____37590
                                                                    ::
                                                                    uu____37610
                                                                     in
                                                                    uu____37556
                                                                    ::
                                                                    uu____37576
                                                                     in
                                                                    uu____37522
                                                                    ::
                                                                    uu____37542
                                                                     in
                                                                    uu____37488
                                                                    ::
                                                                    uu____37508
                                                                     in
                                                                    uu____37454
                                                                    ::
                                                                    uu____37474
                                                                     in
                                                                    uu____37420
                                                                    ::
                                                                    uu____37440
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____37406
                                                                     in
                                                                    uu____37372
                                                                    ::
                                                                    uu____37392
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____37358
                                                                     in
                                                                    uu____37324
                                                                    ::
                                                                    uu____37344
                                                                     in
                                                                    uu____37290
                                                                    ::
                                                                    uu____37310
                                                                     in
                                                                    uu____37256
                                                                    ::
                                                                    uu____37276
                                                                     in
                                                                    uu____37222
                                                                    ::
                                                                    uu____37242
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____37208
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____37194
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____37180
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____37166
                                                                     in
                                                                    uu____37132
                                                                    ::
                                                                    uu____37152
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____37118
                                                                     in
                                                                    uu____37084
                                                                    ::
                                                                    uu____37104
                                                                     in
                                                                    uu____37050
                                                                    ::
                                                                    uu____37070
                                                                     in
                                                                    uu____37016
                                                                    ::
                                                                    uu____37036
                                                                     in
                                                                    uu____36982
                                                                    ::
                                                                    uu____37002
                                                                     in
                                                                    uu____36948
                                                                    ::
                                                                    uu____36968
                                                                     in
                                                                    uu____36914
                                                                    ::
                                                                    uu____36934
                                                                     in
                                                                    uu____36880
                                                                    ::
                                                                    uu____36900
                                                                     in
                                                                    uu____36846
                                                                    ::
                                                                    uu____36866
                                                                     in
                                                                    uu____36812
                                                                    ::
                                                                    uu____36832
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____36798
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____36784
                                                                     in
                                                                    uu____36750
                                                                    ::
                                                                    uu____36770
                                                                     in
                                                                    uu____36716
                                                                    ::
                                                                    uu____36736
                                                                     in
                                                                    uu____36682
                                                                    ::
                                                                    uu____36702
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____36668
                                                                     in
                                                                    uu____36634
                                                                    ::
                                                                    uu____36654
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____36620
                                                                     in
                                                                    uu____36586
                                                                    ::
                                                                    uu____36606
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____36572
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____36558
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____36544
                                                                     in
                                                                    uu____36510
                                                                    ::
                                                                    uu____36530
                                                                     in
                                                                    uu____36476
                                                                    ::
                                                                    uu____36496
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____36462
                                                                     in
                                                                    uu____36428
                                                                    ::
                                                                    uu____36448
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    "Retain comments in the logged SMT queries (requires --log_queries; default true)")
                                                                    ::
                                                                    uu____36414
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____36400
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try initially (default 2)")
                                                                    ::
                                                                    uu____36386
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "protect_top_level_axioms",
                                                                    BoolStr,
                                                                    "Guard nullary top-level symbols in the SMT encoding from provide ambient ground facts (default 'true')")
                                                                    ::
                                                                    uu____36372
                                                                     in
                                                                    uu____36338
                                                                    ::
                                                                    uu____36358
                                                                     in
                                                                  uu____36304
                                                                    ::
                                                                    uu____36324
                                                                   in
                                                                uu____36270
                                                                  ::
                                                                  uu____36290
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "include",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "path")),
                                                                "A directory in which to search for files included on the command line")
                                                                ::
                                                                uu____36256
                                                               in
                                                            uu____36222 ::
                                                              uu____36242
                                                             in
                                                          uu____36188 ::
                                                            uu____36208
                                                           in
                                                        uu____36154 ::
                                                          uu____36174
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "hint_file",
                                                        (PathStr "path"),
                                                        "Read/write hints to <path> (instead of module-specific hints files)")
                                                        :: uu____36140
                                                       in
                                                    uu____36106 ::
                                                      uu____36126
                                                     in
                                                  uu____36072 :: uu____36092
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "extract_namespace",
                                                  (Accumulated
                                                     (PostProcessed
                                                        (pp_lowercase,
                                                          (SimpleStr
                                                             "namespace name")))),
                                                  "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                  :: uu____36058
                                                 in
                                              (FStar_Getopt.noshort,
                                                "extract_module",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "module_name")))),
                                                "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                                :: uu____36044
                                               in
                                            (FStar_Getopt.noshort, "extract",
                                              (Accumulated
                                                 (SimpleStr
                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                              "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                              :: uu____36030
                                             in
                                          uu____35996 :: uu____36016  in
                                        uu____35962 :: uu____35982  in
                                      (FStar_Getopt.noshort, "dump_module",
                                        (Accumulated
                                           (SimpleStr "module_name")), "")
                                        :: uu____35948
                                       in
                                    uu____35914 :: uu____35934  in
                                  uu____35880 :: uu____35900  in
                                uu____35846 :: uu____35866  in
                              (FStar_Getopt.noshort, "dep",
                                (EnumStr ["make"; "graph"; "full"; "raw"]),
                                "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                                :: uu____35832
                               in
                            (FStar_Getopt.noshort, "defensive",
                              (EnumStr ["no"; "warn"; "fail"]),
                              "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                              :: uu____35818
                             in
                          (FStar_Getopt.noshort, "debug_level",
                            (Accumulated
                               (OpenEnumStr
                                  (["Low"; "Medium"; "High"; "Extreme"],
                                    "..."))),
                            "Control the verbosity of debugging info") ::
                            uu____35804
                           in
                        (FStar_Getopt.noshort, "debug",
                          (Accumulated (SimpleStr "module_name")),
                          "Print lots of debugging information while checking module")
                          :: uu____35790
                         in
                      (FStar_Getopt.noshort, "codegen-lib",
                        (Accumulated (SimpleStr "namespace")),
                        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                        :: uu____35776
                       in
                    (FStar_Getopt.noshort, "codegen",
                      (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                      "Generate code for further compilation to executable code, or build a compiler plugin")
                      :: uu____35762
                     in
                  uu____35728 :: uu____35748  in
                uu____35694 :: uu____35714  in
              (FStar_Getopt.noshort, "cache_dir",
                (PostProcessed (pp_validate_dir, (PathStr "dir"))),
                "Read and write .checked and .checked.lax in directory <dir>")
                :: uu____35680
               in
            uu____35646 :: uu____35666  in
          (FStar_Getopt.noshort, "already_cached",
            (Accumulated
               (SimpleStr
                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
            "\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")
            :: uu____35632
           in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____35618
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____35604
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___296_39869  ->
             match uu___296_39869 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____35590

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____39898  ->
    let uu____39901 = specs_with_types ()  in
    FStar_List.map
      (fun uu____39932  ->
         match uu____39932 with
         | (short,long,typ,doc) ->
             let uu____39954 =
               let uu____39968 = arg_spec_of_opt_type long typ  in
               (short, long, uu____39968, doc)  in
             mk_spec uu____39954) uu____39901

let (settable : Prims.string -> Prims.bool) =
  fun uu___297_39983  ->
    match uu___297_39983 with
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
    | uu____40106 -> false
  
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
       (fun uu____40205  ->
          match uu____40205 with
          | (uu____40220,x,uu____40222,uu____40223) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____40298  ->
          match uu____40298 with
          | (uu____40313,x,uu____40315,uu____40316) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____40332  ->
    let uu____40333 = specs ()  in display_usage_aux uu____40333
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____40365 -> true
    | uu____40368 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____40378 -> uu____40378
  
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
        (fun uu___759_40399  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____40416 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____40416
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____40441  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____40447 =
             let uu____40451 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____40451 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____40447)
       in
    let uu____40508 =
      let uu____40512 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____40512
       in
    (res, uu____40508)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____40554  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____40597 = specs ()  in
       FStar_Getopt.parse_cmdline uu____40597 (fun x  -> ())  in
     (let uu____40604 =
        let uu____40610 =
          let uu____40611 = FStar_List.map mk_string old_verify_module  in
          List uu____40611  in
        ("verify_module", uu____40610)  in
      set_option' uu____40604);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____40630 =
        let uu____40632 =
          let uu____40634 =
            let uu____40636 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____40636  in
          (FStar_String.length f1) - uu____40634  in
        uu____40632 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____40630  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____40649 = get_lax ()  in
    if uu____40649
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____40670 = module_name_of_file_name fn  in
    should_verify uu____40670
  
let (module_name_eq : Prims.string -> Prims.string -> Prims.bool) =
  fun m1  ->
    fun m2  -> (FStar_String.lowercase m1) = (FStar_String.lowercase m2)
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____40698 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____40698 (FStar_List.existsb (module_name_eq m))
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____40716 = should_verify m  in
    if uu____40716 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____40733  ->
    let cache_dir =
      let uu____40738 = get_cache_dir ()  in
      match uu____40738 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some c -> [c]  in
    let uu____40752 = get_no_default_includes ()  in
    if uu____40752
    then
      let uu____40758 = get_include ()  in
      FStar_List.append cache_dir uu____40758
    else
      (let lib_paths =
         let uu____40769 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____40769 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = FStar_String.op_Hat fstar_bin_directory "/.."
                in
             let defs = universe_include_path_base_dirs  in
             let uu____40785 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> FStar_String.op_Hat fstar_home x))
                in
             FStar_All.pipe_right uu____40785
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____40812 =
         let uu____40816 =
           let uu____40820 = get_include ()  in
           FStar_List.append uu____40820 ["."]  in
         FStar_List.append lib_paths uu____40816  in
       FStar_List.append cache_dir uu____40812)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____40847 = FStar_Util.smap_try_find file_map filename  in
    match uu____40847 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___810_40869  ->
               match () with
               | () ->
                   let uu____40873 = FStar_Util.is_path_absolute filename  in
                   if uu____40873
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____40889 =
                        let uu____40893 = include_path ()  in
                        FStar_List.rev uu____40893  in
                      FStar_Util.find_map uu____40889
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___809_40921 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____40941  ->
    let uu____40942 = get_prims ()  in
    match uu____40942 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____40951 = find_file filename  in
        (match uu____40951 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____40960 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____40960)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____40973  ->
    let uu____40974 = prims ()  in FStar_Util.basename uu____40974
  
let (pervasives : unit -> Prims.string) =
  fun uu____40982  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____40986 = find_file filename  in
    match uu____40986 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____40995 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____40995
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____41005  ->
    let uu____41006 = pervasives ()  in FStar_Util.basename uu____41006
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____41014  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____41018 = find_file filename  in
    match uu____41018 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____41027 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____41027
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____41040 = get_odir ()  in
    match uu____41040 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____41058 = get_cache_dir ()  in
    match uu____41058 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____41067 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____41067
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns  ->
    let cache = FStar_Util.smap_create (Prims.parse_int "31")  in
    let with_cache f s =
      let uu____41189 = FStar_Util.smap_try_find cache s  in
      match uu____41189 with
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
             let uu____41324 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____41324  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____41347 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              let s1 = FStar_Util.trim_string s  in
              if s1 = ""
              then []
              else
                with_cache
                  (fun s2  ->
                     let uu____41415 =
                       FStar_All.pipe_right (FStar_Util.splitlines s2)
                         (FStar_List.concatMap
                            (fun s3  -> FStar_Util.split s3 " "))
                        in
                     FStar_All.pipe_right uu____41415
                       (FStar_List.map parse_one_setting)) s1))
       in
    FStar_All.pipe_right uu____41347 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____41490 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____41490 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____41505  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____41514  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____41523  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____41530  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____41537  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____41544  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____41554 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____41565 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____41576 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____41587 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____41596  ->
    let uu____41597 = get_codegen ()  in
    FStar_Util.map_opt uu____41597
      (fun uu___298_41603  ->
         match uu___298_41603 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____41609 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____41622  ->
    let uu____41623 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____41623
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____41649  -> let uu____41650 = get_debug ()  in uu____41650 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____41667 = get_debug ()  in
    FStar_All.pipe_right uu____41667
      (FStar_List.existsb (module_name_eq modul))
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____41692 = get_debug ()  in
       FStar_All.pipe_right uu____41692
         (FStar_List.existsb (module_name_eq modul)))
        && (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____41707  ->
    let uu____41708 = get_defensive ()  in uu____41708 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____41718  ->
    let uu____41719 = get_defensive ()  in uu____41719 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____41731  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____41738  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____41745  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____41752  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____41762 = get_dump_module ()  in
    FStar_All.pipe_right uu____41762 (FStar_List.existsb (module_name_eq s))
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____41777  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____41784  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____41794 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____41794
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____41830  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____41838  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____41845  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____41854  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____41861  -> get_ide () 
let (print : unit -> Prims.bool) = fun uu____41868  -> get_print () 
let (print_in_place : unit -> Prims.bool) =
  fun uu____41875  -> get_print_in_place () 
let profile : 'a . (unit -> 'a) -> ('a -> Prims.string) -> 'a =
  fun f  ->
    fun msg  ->
      let uu____41906 = get_profile ()  in
      if uu____41906
      then
        let uu____41909 = FStar_Util.record_time f  in
        match uu____41909 with
        | (a,time) ->
            ((let uu____41920 = FStar_Util.string_of_int time  in
              let uu____41922 = msg a  in
              FStar_Util.print2 "Elapsed time %s ms: %s\n" uu____41920
                uu____41922);
             a)
      else f ()
  
let (protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____41933  -> get_protect_top_level_axioms () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____41940  ->
    let uu____41941 = get_initial_fuel ()  in
    let uu____41943 = get_max_fuel ()  in Prims.min uu____41941 uu____41943
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____41951  ->
    let uu____41952 = get_initial_ifuel ()  in
    let uu____41954 = get_max_ifuel ()  in Prims.min uu____41952 uu____41954
  
let (interactive : unit -> Prims.bool) =
  fun uu____41962  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____41969  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____41978  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____41985  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____41992  -> get_log_queries () 
let (keep_query_captions : unit -> Prims.bool) =
  fun uu____41999  -> (log_queries ()) && (get_keep_query_captions ()) 
let (log_types : unit -> Prims.bool) = fun uu____42006  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____42013  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____42020  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____42027  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____42034  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____42040  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____42049  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____42056  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____42066 = get_no_extract ()  in
    FStar_All.pipe_right uu____42066 (FStar_List.existsb (module_name_eq s))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____42081  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____42088  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____42095  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____42102  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____42111  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____42118  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____42125  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____42132  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____42139  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____42146  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____42153  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____42160  -> get_print_z3_statistics () 
let (query_stats : unit -> Prims.bool) =
  fun uu____42167  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____42174  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____42183  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____42190  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____42197  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____42204  ->
    let uu____42205 = get_smtencoding_nl_arith_repr ()  in
    uu____42205 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____42215  ->
    let uu____42216 = get_smtencoding_nl_arith_repr ()  in
    uu____42216 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____42226  ->
    let uu____42227 = get_smtencoding_nl_arith_repr ()  in
    uu____42227 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____42237  ->
    let uu____42238 = get_smtencoding_l_arith_repr ()  in
    uu____42238 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____42248  ->
    let uu____42249 = get_smtencoding_l_arith_repr ()  in
    uu____42249 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____42259  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____42266  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____42273  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____42280  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____42287  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____42294  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____42301  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____42308  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____42315  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____42322  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____42329  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____42336  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____42343  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____42350  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____42359  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____42366  -> get_use_tactics () 
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu____42382  ->
    let uu____42383 = get_using_facts_from ()  in
    match uu____42383 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____42437  ->
    let uu____42438 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____42438
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____42449  ->
    let uu____42450 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____42450 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____42458 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____42469  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____42476  ->
    let uu____42477 = get_smt ()  in
    match uu____42477 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____42495  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____42502  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____42509  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____42516  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____42523  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____42530  ->
    (get_use_two_phase_tc ()) &&
      (let uu____42532 = lax ()  in Prims.op_Negation uu____42532)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____42540  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____42547  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____42554  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____42561  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____42568  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____42585 =
      let uu____42587 = trace_error ()  in Prims.op_Negation uu____42587  in
    if uu____42585
    then
      (push ();
       (let r =
          try
            (fun uu___1009_42602  ->
               match () with
               | () -> let uu____42607 = f ()  in FStar_Util.Inr uu____42607)
              ()
          with | uu___1008_42609 -> FStar_Util.Inl uu___1008_42609  in
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
        | (uu____42690,[]) -> true
        | (m2::ms,p::ps) ->
            (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
        | uu____42723 -> false  in
      let uu____42735 =
        FStar_All.pipe_right setting
          (FStar_Util.try_find
             (fun uu____42777  ->
                match uu____42777 with
                | (path,uu____42788) -> matches_path m_components path))
         in
      match uu____42735 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____42807,flag) -> flag
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____42836 = get_extract ()  in
    match uu____42836 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____42851 =
            let uu____42867 = get_no_extract ()  in
            let uu____42871 = get_extract_namespace ()  in
            let uu____42875 = get_extract_module ()  in
            (uu____42867, uu____42871, uu____42875)  in
          match uu____42851 with
          | ([],[],[]) -> ()
          | uu____42900 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         module_matches_namespace_filter m1 extract_setting)
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____42929 = get_extract_namespace ()  in
          match uu____42929 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____42957 = get_extract_module ()  in
          match uu____42957 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____42979 = no_extract m1  in Prims.op_Negation uu____42979)
          &&
          (let uu____42982 =
             let uu____42993 = get_extract_namespace ()  in
             let uu____42997 = get_extract_module ()  in
             (uu____42993, uu____42997)  in
           (match uu____42982 with
            | ([],[]) -> true
            | uu____43017 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  
let (should_be_already_cached : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____43037 = get_already_cached ()  in
    match uu____43037 with
    | FStar_Pervasives_Native.None  -> false
    | FStar_Pervasives_Native.Some already_cached_setting ->
        module_matches_namespace_filter m already_cached_setting
  
let (error_flags : unit -> error_flag Prims.list) =
  let cache = FStar_Util.smap_create (Prims.parse_int "10")  in
  fun uu____43070  ->
    let we = warn_error ()  in
    let uu____43073 = FStar_Util.smap_try_find cache we  in
    match uu____43073 with
    | FStar_Pervasives_Native.None  ->
        let r = parse_warn_error we  in (FStar_Util.smap_add cache we r; r)
    | FStar_Pervasives_Native.Some r -> r
  