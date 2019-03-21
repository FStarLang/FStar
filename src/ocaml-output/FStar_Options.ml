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
    match projectee with | Low  -> true | uu____30548 -> false
  
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____30559 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | High  -> true | uu____30570 -> false
  
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____30581 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____30594 -> false
  
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
    match projectee with | Bool _0 -> true | uu____30648 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____30671 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____30694 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____30717 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____30741 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____30765 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _30773  -> Bool _30773 
let (mk_string : Prims.string -> option_val) = fun _30780  -> String _30780 
let (mk_path : Prims.string -> option_val) = fun _30787  -> Path _30787 
let (mk_int : Prims.int -> option_val) = fun _30794  -> Int _30794 
let (mk_list : option_val Prims.list -> option_val) =
  fun _30802  -> List _30802 
type options =
  | Set 
  | Reset 
  | Restore 
let (uu___is_Set : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Set  -> true | uu____30812 -> false
  
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____30823 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____30834 -> false
  
type error_flag =
  | CFatal 
  | CAlwaysError 
  | CError 
  | CWarning 
  | CSilent 
let (uu___is_CFatal : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CFatal  -> true | uu____30845 -> false
  
let (uu___is_CAlwaysError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CAlwaysError  -> true | uu____30856 -> false
  
let (uu___is_CError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CError  -> true | uu____30867 -> false
  
let (uu___is_CWarning : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CWarning  -> true | uu____30878 -> false
  
let (uu___is_CSilent : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CSilent  -> true | uu____30889 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____30903  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____30930  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____30958  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___289_30987  ->
    match uu___289_30987 with
    | Bool b -> b
    | uu____30991 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___290_31000  ->
    match uu___290_31000 with
    | Int b -> b
    | uu____31004 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___291_31013  ->
    match uu___291_31013 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____31019 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___292_31029  ->
    match uu___292_31029 with
    | List ts -> ts
    | uu____31035 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____31046 .
    (option_val -> 'Auu____31046) -> option_val -> 'Auu____31046 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____31064 = as_list' x  in
      FStar_All.pipe_right uu____31064 (FStar_List.map as_t)
  
let as_option :
  'Auu____31078 .
    (option_val -> 'Auu____31078) ->
      option_val -> 'Auu____31078 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___293_31093  ->
      match uu___293_31093 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____31097 = as_t v1  in
          FStar_Pervasives_Native.Some uu____31097
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___294_31106  ->
    match uu___294_31106 with
    | List ls ->
        let uu____31113 =
          FStar_List.map
            (fun l  ->
               let uu____31125 = as_string l  in
               FStar_Util.split uu____31125 ",") ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____31113
    | uu____31137 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let copy_optionstate :
  'Auu____31149 .
    'Auu____31149 FStar_Util.smap -> 'Auu____31149 FStar_Util.smap
  = fun m  -> FStar_Util.smap_copy m 
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (internal_peek : unit -> optionstate) =
  fun uu____31179  ->
    let uu____31180 =
      let uu____31183 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____31183  in
    FStar_List.hd uu____31180
  
let (peek : unit -> optionstate) = fun uu____31222  -> internal_peek () 
let (pop : unit -> unit) =
  fun uu____31228  ->
    let uu____31229 = FStar_ST.op_Bang fstar_options  in
    match uu____31229 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____31264::[] -> failwith "TOO MANY POPS!"
    | uu____31272::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____31314  ->
    let uu____31315 =
      let uu____31320 =
        let uu____31323 =
          let uu____31326 = FStar_ST.op_Bang fstar_options  in
          FStar_List.hd uu____31326  in
        FStar_List.map copy_optionstate uu____31323  in
      let uu____31360 = FStar_ST.op_Bang fstar_options  in uu____31320 ::
        uu____31360
       in
    FStar_ST.op_Colon_Equals fstar_options uu____31315
  
let (internal_pop : unit -> Prims.bool) =
  fun uu____31427  ->
    let curstack =
      let uu____31431 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____31431  in
    match curstack with
    | [] -> failwith "impossible: empty current option stack"
    | uu____31468::[] -> false
    | uu____31470::tl1 ->
        ((let uu____31475 =
            let uu____31480 =
              let uu____31485 = FStar_ST.op_Bang fstar_options  in
              FStar_List.tl uu____31485  in
            tl1 :: uu____31480  in
          FStar_ST.op_Colon_Equals fstar_options uu____31475);
         true)
  
let (internal_push : unit -> unit) =
  fun uu____31554  ->
    let curstack =
      let uu____31558 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____31558  in
    let stack' =
      let uu____31595 =
        let uu____31596 = FStar_List.hd curstack  in
        copy_optionstate uu____31596  in
      uu____31595 :: curstack  in
    let uu____31599 =
      let uu____31604 =
        let uu____31609 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____31609  in
      stack' :: uu____31604  in
    FStar_ST.op_Colon_Equals fstar_options uu____31599
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____31678 = FStar_ST.op_Bang fstar_options  in
    match uu____31678 with
    | [] -> failwith "set on empty option stack"
    | []::uu____31713 -> failwith "set on empty current option stack"
    | (uu____31721::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
  
let (snapshot : unit -> (Prims.int * unit)) =
  fun uu____31771  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____31801 = peek ()  in FStar_Util.smap_add uu____31801 k v1
  
let (set_option' : (Prims.string * option_val) -> unit) =
  fun uu____31814  -> match uu____31814 with | (k,v1) -> set_option k v1 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____31842 =
      let uu____31846 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____31846
       in
    FStar_ST.op_Colon_Equals light_off_files uu____31842
  
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
    let uu____32816 = FStar_ST.op_Bang r  in
    match uu____32816 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some f)
    | uu____32907 -> failwith "Multiple initialization of FStar.Options"  in
  let get1 uu____32928 =
    let uu____32929 = FStar_ST.op_Bang r  in
    match uu____32929 with
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
    let uu____33068 = FStar_Pervasives_Native.snd parse_warn_error_set_get ()
       in
    uu____33068 s
  
let (init : unit -> unit) =
  fun uu____33099  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____33119  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____33192 =
      let uu____33195 = peek ()  in FStar_Util.smap_try_find uu____33195 s
       in
    match uu____33192 with
    | FStar_Pervasives_Native.None  ->
        let uu____33198 =
          let uu____33200 = FStar_String.op_Hat s " not found"  in
          FStar_String.op_Hat "Impossible: option " uu____33200  in
        failwith uu____33198
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____33212 .
    Prims.string -> (option_val -> 'Auu____33212) -> 'Auu____33212
  = fun s  -> fun c  -> let uu____33230 = get_option s  in c uu____33230 
let (get_abort_on : unit -> Prims.int) =
  fun uu____33237  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____33246  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____33257  -> lookup_opt "admit_except" (as_option as_string) 
let (get_already_cached :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____33273  ->
    lookup_opt "already_cached" (as_option (as_list as_string))
  
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____33290  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33301  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____33313  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____33322  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33333  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____33347  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____33361  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____33375  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____33386  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33397  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____33409  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____33418  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____33427  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____33438  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____33450  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____33459  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____33472  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____33491  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____33505  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____33517  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____33526  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____33535  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33546  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____33558  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____33567  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____33578  -> lookup_opt "include" (as_list as_string) 
let (get_print : unit -> Prims.bool) =
  fun uu____33590  -> lookup_opt "print" as_bool 
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____33599  -> lookup_opt "print_in_place" as_bool 
let (get_profile : unit -> Prims.bool) =
  fun uu____33608  -> lookup_opt "profile" as_bool 
let (get_protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____33617  -> lookup_opt "protect_top_level_axioms" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____33626  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____33635  -> lookup_opt "initial_ifuel" as_int 
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu____33644  -> lookup_opt "keep_query_captions" as_bool 
let (get_lax : unit -> Prims.bool) =
  fun uu____33653  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____33664  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____33676  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____33685  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____33694  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____33703  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____33712  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____33721  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____33730  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____33739  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____33750  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____33762  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____33771  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____33780  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____33789  ->
    lookup_opt "normalize_pure_terms_for_extraction" as_bool
  
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33800  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____33812  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33823  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____33835  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____33844  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____33853  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____33862  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____33871  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____33880  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____33889  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____33898  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____33907  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33918  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____33930  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____33941  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____33953  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____33962  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____33971  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____33980  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____33989  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____33998  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____34007  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____34016  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____34025  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____34034  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____34043  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____34052  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____34061  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____34070  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____34079  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____34088  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____34097  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____34108  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____34120  ->
    let uu____34121 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____34121
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____34135  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____34154  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____34168  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____34182  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____34194  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____34203  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____34214  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____34226  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____34235  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____34244  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____34253  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____34262  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____34271  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____34280  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____34289  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____34298  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____34307  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___295_34316  ->
    match uu___295_34316 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____34337 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____34346 = get_debug_level ()  in
    FStar_All.pipe_right uu____34346
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "<not set>" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____34402  ->
    let uu____34403 =
      let uu____34405 = FStar_ST.op_Bang _version  in
      let uu____34428 = FStar_ST.op_Bang _platform  in
      let uu____34451 = FStar_ST.op_Bang _compiler  in
      let uu____34474 = FStar_ST.op_Bang _date  in
      let uu____34497 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____34405
        uu____34428 uu____34451 uu____34474 uu____34497
       in
    FStar_Util.print_string uu____34403
  
let display_usage_aux :
  'Auu____34528 'Auu____34529 .
    ('Auu____34528 * Prims.string * 'Auu____34529 FStar_Getopt.opt_variant *
      Prims.string) Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____34584  ->
         match uu____34584 with
         | (uu____34597,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____34616 =
                      let uu____34618 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____34618  in
                    FStar_Util.print_string uu____34616
                  else
                    (let uu____34623 =
                       let uu____34625 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____34625 doc  in
                     FStar_Util.print_string uu____34623)
              | FStar_Getopt.OneArg (uu____34628,argname) ->
                  if doc = ""
                  then
                    let uu____34643 =
                      let uu____34645 = FStar_Util.colorize_bold flag  in
                      let uu____34647 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____34645
                        uu____34647
                       in
                    FStar_Util.print_string uu____34643
                  else
                    (let uu____34652 =
                       let uu____34654 = FStar_Util.colorize_bold flag  in
                       let uu____34656 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____34654
                         uu____34656 doc
                        in
                     FStar_Util.print_string uu____34652))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____34691 = o  in
    match uu____34691 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____34733 =
                let uu____34734 = f ()  in set_option name uu____34734  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____34755 = f x  in set_option name uu____34755
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____34782 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____34782  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____34808 =
        let uu____34811 = lookup_opt name as_list'  in
        FStar_List.append uu____34811 [value]  in
      mk_list uu____34808
  
let accumulate_string :
  'Auu____34825 .
    Prims.string -> ('Auu____34825 -> Prims.string) -> 'Auu____34825 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____34850 =
          let uu____34851 =
            let uu____34852 = post_processor value  in mk_string uu____34852
             in
          accumulated_option name uu____34851  in
        set_option name uu____34850
  
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
    match projectee with | Const _0 -> true | uu____34974 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____34994 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____35015 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____35028 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____35051 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____35076 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____35112 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____35162 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____35202 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____35221 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____35247 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____35290 -> true
    | uu____35293 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____35303 -> uu____35303
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___581_35327  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____35329 ->
                      let uu____35331 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____35331 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____35339 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____35339
                  | PathStr uu____35356 -> mk_path str_val
                  | SimpleStr uu____35358 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____35368 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____35385 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____35385
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
            let uu____35405 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____35405
  
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ  ->
    let desc_of_enum cases =
      let uu____35435 =
        let uu____35437 =
          FStar_String.op_Hat (FStar_String.concat "|" cases) "]"  in
        FStar_String.op_Hat "[" uu____35437  in
      FStar_Pervasives_Native.Some uu____35435  in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____35479,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____35489,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____35520 = desc_of_opt_type typ  in
      match uu____35520 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____35528  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____35554 =
      let uu____35556 = as_string s  in FStar_String.lowercase uu____35556
       in
    mk_string uu____35554
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string)
      Prims.list)
  =
  fun uu____35591  ->
    let uu____35605 =
      let uu____35619 =
        let uu____35633 =
          let uu____35647 =
            let uu____35661 =
              let uu____35673 =
                let uu____35674 = mk_bool true  in Const uu____35674  in
              (FStar_Getopt.noshort, "cache_checked_modules", uu____35673,
                "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
               in
            let uu____35681 =
              let uu____35695 =
                let uu____35709 =
                  let uu____35721 =
                    let uu____35722 = mk_bool true  in Const uu____35722  in
                  (FStar_Getopt.noshort, "cache_off", uu____35721,
                    "Do not read or write any .checked files")
                   in
                let uu____35729 =
                  let uu____35743 =
                    let uu____35755 =
                      let uu____35756 = mk_bool true  in Const uu____35756
                       in
                    (FStar_Getopt.noshort, "cmi", uu____35755,
                      "Inline across module interfaces during extraction (aka. cross-module inlining)")
                     in
                  let uu____35763 =
                    let uu____35777 =
                      let uu____35791 =
                        let uu____35805 =
                          let uu____35819 =
                            let uu____35833 =
                              let uu____35847 =
                                let uu____35861 =
                                  let uu____35873 =
                                    let uu____35874 = mk_bool true  in
                                    Const uu____35874  in
                                  (FStar_Getopt.noshort, "detail_errors",
                                    uu____35873,
                                    "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                   in
                                let uu____35881 =
                                  let uu____35895 =
                                    let uu____35907 =
                                      let uu____35908 = mk_bool true  in
                                      Const uu____35908  in
                                    (FStar_Getopt.noshort,
                                      "detail_hint_replay", uu____35907,
                                      "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                     in
                                  let uu____35915 =
                                    let uu____35929 =
                                      let uu____35941 =
                                        let uu____35942 = mk_bool true  in
                                        Const uu____35942  in
                                      (FStar_Getopt.noshort, "doc",
                                        uu____35941,
                                        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                       in
                                    let uu____35949 =
                                      let uu____35963 =
                                        let uu____35977 =
                                          let uu____35989 =
                                            let uu____35990 = mk_bool true
                                               in
                                            Const uu____35990  in
                                          (FStar_Getopt.noshort,
                                            "eager_inference", uu____35989,
                                            "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                           in
                                        let uu____35997 =
                                          let uu____36011 =
                                            let uu____36023 =
                                              let uu____36024 = mk_bool true
                                                 in
                                              Const uu____36024  in
                                            (FStar_Getopt.noshort,
                                              "eager_subtyping", uu____36023,
                                              "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                             in
                                          let uu____36031 =
                                            let uu____36045 =
                                              let uu____36059 =
                                                let uu____36073 =
                                                  let uu____36087 =
                                                    let uu____36099 =
                                                      let uu____36100 =
                                                        mk_bool true  in
                                                      Const uu____36100  in
                                                    (FStar_Getopt.noshort,
                                                      "expose_interfaces",
                                                      uu____36099,
                                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                     in
                                                  let uu____36107 =
                                                    let uu____36121 =
                                                      let uu____36133 =
                                                        let uu____36134 =
                                                          mk_bool true  in
                                                        Const uu____36134  in
                                                      (FStar_Getopt.noshort,
                                                        "hide_uvar_nums",
                                                        uu____36133,
                                                        "Don't print unification variable numbers")
                                                       in
                                                    let uu____36141 =
                                                      let uu____36155 =
                                                        let uu____36169 =
                                                          let uu____36181 =
                                                            let uu____36182 =
                                                              mk_bool true
                                                               in
                                                            Const uu____36182
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "hint_info",
                                                            uu____36181,
                                                            "Print information regarding hints (deprecated; use --query_stats instead)")
                                                           in
                                                        let uu____36189 =
                                                          let uu____36203 =
                                                            let uu____36215 =
                                                              let uu____36216
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____36216
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "in",
                                                              uu____36215,
                                                              "Legacy interactive mode; reads input from stdin")
                                                             in
                                                          let uu____36223 =
                                                            let uu____36237 =
                                                              let uu____36249
                                                                =
                                                                let uu____36250
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____36250
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "ide",
                                                                uu____36249,
                                                                "JSON-based interactive mode for IDEs")
                                                               in
                                                            let uu____36257 =
                                                              let uu____36271
                                                                =
                                                                let uu____36285
                                                                  =
                                                                  let uu____36297
                                                                    =
                                                                    let uu____36298
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36298
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "print",
                                                                    uu____36297,
                                                                    "Parses and prettyprints the files included on the command line")
                                                                   in
                                                                let uu____36305
                                                                  =
                                                                  let uu____36319
                                                                    =
                                                                    let uu____36331
                                                                    =
                                                                    let uu____36332
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36332
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_in_place",
                                                                    uu____36331,
                                                                    "Parses and prettyprints in place the files included on the command line")
                                                                     in
                                                                  let uu____36339
                                                                    =
                                                                    let uu____36353
                                                                    =
                                                                    let uu____36365
                                                                    =
                                                                    let uu____36366
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36366
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "profile",
                                                                    uu____36365,
                                                                    "Prints timing information for various operations in the compiler")
                                                                     in
                                                                    let uu____36373
                                                                    =
                                                                    let uu____36387
                                                                    =
                                                                    let uu____36401
                                                                    =
                                                                    let uu____36415
                                                                    =
                                                                    let uu____36429
                                                                    =
                                                                    let uu____36443
                                                                    =
                                                                    let uu____36455
                                                                    =
                                                                    let uu____36456
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36456
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____36455,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____36463
                                                                    =
                                                                    let uu____36477
                                                                    =
                                                                    let uu____36491
                                                                    =
                                                                    let uu____36503
                                                                    =
                                                                    let uu____36504
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36504
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____36503,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____36511
                                                                    =
                                                                    let uu____36525
                                                                    =
                                                                    let uu____36537
                                                                    =
                                                                    let uu____36538
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36538
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____36537,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____36545
                                                                    =
                                                                    let uu____36559
                                                                    =
                                                                    let uu____36573
                                                                    =
                                                                    let uu____36587
                                                                    =
                                                                    let uu____36601
                                                                    =
                                                                    let uu____36613
                                                                    =
                                                                    let uu____36614
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36614
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____36613,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____36621
                                                                    =
                                                                    let uu____36635
                                                                    =
                                                                    let uu____36649
                                                                    =
                                                                    let uu____36661
                                                                    =
                                                                    let uu____36662
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36662
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____36661,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____36669
                                                                    =
                                                                    let uu____36683
                                                                    =
                                                                    let uu____36697
                                                                    =
                                                                    let uu____36709
                                                                    =
                                                                    let uu____36710
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36710
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____36709,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____36717
                                                                    =
                                                                    let uu____36731
                                                                    =
                                                                    let uu____36743
                                                                    =
                                                                    let uu____36744
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36744
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____36743,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____36751
                                                                    =
                                                                    let uu____36765
                                                                    =
                                                                    let uu____36777
                                                                    =
                                                                    let uu____36778
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36778
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____36777,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____36785
                                                                    =
                                                                    let uu____36799
                                                                    =
                                                                    let uu____36813
                                                                    =
                                                                    let uu____36827
                                                                    =
                                                                    let uu____36839
                                                                    =
                                                                    let uu____36840
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36840
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____36839,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____36847
                                                                    =
                                                                    let uu____36861
                                                                    =
                                                                    let uu____36873
                                                                    =
                                                                    let uu____36874
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36874
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____36873,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____36881
                                                                    =
                                                                    let uu____36895
                                                                    =
                                                                    let uu____36907
                                                                    =
                                                                    let uu____36908
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36908
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____36907,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____36915
                                                                    =
                                                                    let uu____36929
                                                                    =
                                                                    let uu____36941
                                                                    =
                                                                    let uu____36942
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36942
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____36941,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____36949
                                                                    =
                                                                    let uu____36963
                                                                    =
                                                                    let uu____36975
                                                                    =
                                                                    let uu____36976
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____36976
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____36975,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____36983
                                                                    =
                                                                    let uu____36997
                                                                    =
                                                                    let uu____37009
                                                                    =
                                                                    let uu____37010
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37010
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____37009,
                                                                    "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)")
                                                                     in
                                                                    let uu____37017
                                                                    =
                                                                    let uu____37031
                                                                    =
                                                                    let uu____37043
                                                                    =
                                                                    let uu____37044
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37044
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____37043,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____37051
                                                                    =
                                                                    let uu____37065
                                                                    =
                                                                    let uu____37077
                                                                    =
                                                                    let uu____37078
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37078
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____37077,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____37085
                                                                    =
                                                                    let uu____37099
                                                                    =
                                                                    let uu____37111
                                                                    =
                                                                    let uu____37112
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37112
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____37111,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____37119
                                                                    =
                                                                    let uu____37133
                                                                    =
                                                                    let uu____37147
                                                                    =
                                                                    let uu____37159
                                                                    =
                                                                    let uu____37160
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37160
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____37159,
                                                                    "Disable all non-critical output")
                                                                     in
                                                                    let uu____37167
                                                                    =
                                                                    let uu____37181
                                                                    =
                                                                    let uu____37195
                                                                    =
                                                                    let uu____37209
                                                                    =
                                                                    let uu____37223
                                                                    =
                                                                    let uu____37237
                                                                    =
                                                                    let uu____37249
                                                                    =
                                                                    let uu____37250
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37250
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____37249,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____37257
                                                                    =
                                                                    let uu____37271
                                                                    =
                                                                    let uu____37283
                                                                    =
                                                                    let uu____37284
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37284
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____37283,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____37291
                                                                    =
                                                                    let uu____37305
                                                                    =
                                                                    let uu____37317
                                                                    =
                                                                    let uu____37318
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37318
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____37317,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____37325
                                                                    =
                                                                    let uu____37339
                                                                    =
                                                                    let uu____37351
                                                                    =
                                                                    let uu____37352
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37352
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____37351,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____37359
                                                                    =
                                                                    let uu____37373
                                                                    =
                                                                    let uu____37387
                                                                    =
                                                                    let uu____37399
                                                                    =
                                                                    let uu____37400
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37400
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____37399,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____37407
                                                                    =
                                                                    let uu____37421
                                                                    =
                                                                    let uu____37435
                                                                    =
                                                                    let uu____37447
                                                                    =
                                                                    let uu____37448
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37448
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____37447,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____37455
                                                                    =
                                                                    let uu____37469
                                                                    =
                                                                    let uu____37481
                                                                    =
                                                                    let uu____37482
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37482
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____37481,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____37489
                                                                    =
                                                                    let uu____37503
                                                                    =
                                                                    let uu____37515
                                                                    =
                                                                    let uu____37516
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37516
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____37515,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____37523
                                                                    =
                                                                    let uu____37537
                                                                    =
                                                                    let uu____37549
                                                                    =
                                                                    let uu____37550
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37550
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____37549,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____37557
                                                                    =
                                                                    let uu____37571
                                                                    =
                                                                    let uu____37583
                                                                    =
                                                                    let uu____37584
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37584
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____37583,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____37591
                                                                    =
                                                                    let uu____37605
                                                                    =
                                                                    let uu____37617
                                                                    =
                                                                    let uu____37618
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37618
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____37617,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____37625
                                                                    =
                                                                    let uu____37639
                                                                    =
                                                                    let uu____37651
                                                                    =
                                                                    let uu____37652
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37652
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____37651,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____37659
                                                                    =
                                                                    let uu____37673
                                                                    =
                                                                    let uu____37685
                                                                    =
                                                                    let uu____37686
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37686
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____37685,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____37693
                                                                    =
                                                                    let uu____37707
                                                                    =
                                                                    let uu____37721
                                                                    =
                                                                    let uu____37733
                                                                    =
                                                                    let uu____37734
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37734
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____37733,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____37741
                                                                    =
                                                                    let uu____37755
                                                                    =
                                                                    let uu____37767
                                                                    =
                                                                    let uu____37768
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37768
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____37767,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____37775
                                                                    =
                                                                    let uu____37789
                                                                    =
                                                                    let uu____37803
                                                                    =
                                                                    let uu____37817
                                                                    =
                                                                    let uu____37831
                                                                    =
                                                                    let uu____37843
                                                                    =
                                                                    let uu____37844
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37844
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____37843,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____37851
                                                                    =
                                                                    let uu____37865
                                                                    =
                                                                    let uu____37877
                                                                    =
                                                                    let uu____37878
                                                                    =
                                                                    let uu____37886
                                                                    =
                                                                    let uu____37887
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37887
                                                                     in
                                                                    ((fun
                                                                    uu____37894
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____37886)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____37878
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____37877,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____37903
                                                                    =
                                                                    let uu____37917
                                                                    =
                                                                    let uu____37929
                                                                    =
                                                                    let uu____37930
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37930
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____37929,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____37937
                                                                    =
                                                                    let uu____37951
                                                                    =
                                                                    let uu____37965
                                                                    =
                                                                    let uu____37977
                                                                    =
                                                                    let uu____37978
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____37978
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____37977,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____37985
                                                                    =
                                                                    let uu____37999
                                                                    =
                                                                    let uu____38013
                                                                    =
                                                                    let uu____38027
                                                                    =
                                                                    let uu____38041
                                                                    =
                                                                    let uu____38055
                                                                    =
                                                                    let uu____38067
                                                                    =
                                                                    let uu____38068
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38068
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____38067,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____38075
                                                                    =
                                                                    let uu____38089
                                                                    =
                                                                    let uu____38101
                                                                    =
                                                                    let uu____38102
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38102
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____38101,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____38109
                                                                    =
                                                                    let uu____38123
                                                                    =
                                                                    let uu____38137
                                                                    =
                                                                    let uu____38151
                                                                    =
                                                                    let uu____38165
                                                                    =
                                                                    let uu____38177
                                                                    =
                                                                    let uu____38178
                                                                    =
                                                                    let uu____38186
                                                                    =
                                                                    let uu____38187
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38187
                                                                     in
                                                                    ((fun
                                                                    uu____38193
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____38186)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____38178
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____38177,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____38221
                                                                    =
                                                                    let uu____38235
                                                                    =
                                                                    let uu____38247
                                                                    =
                                                                    let uu____38248
                                                                    =
                                                                    let uu____38256
                                                                    =
                                                                    let uu____38257
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38257
                                                                     in
                                                                    ((fun
                                                                    uu____38263
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____38256)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____38248
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____38247,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____38291
                                                                    =
                                                                    let uu____38305
                                                                    =
                                                                    let uu____38317
                                                                    =
                                                                    let uu____38318
                                                                    =
                                                                    let uu____38326
                                                                    =
                                                                    let uu____38327
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____38327
                                                                     in
                                                                    ((fun
                                                                    uu____38334
                                                                     ->
                                                                    (
                                                                    let uu____38336
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____38336);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____38326)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____38318
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____38317,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____38305]
                                                                     in
                                                                    uu____38235
                                                                    ::
                                                                    uu____38291
                                                                     in
                                                                    uu____38165
                                                                    ::
                                                                    uu____38221
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____38151
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____38137
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____38123
                                                                     in
                                                                    uu____38089
                                                                    ::
                                                                    uu____38109
                                                                     in
                                                                    uu____38055
                                                                    ::
                                                                    uu____38075
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____38041
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____38027
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____38013
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____37999
                                                                     in
                                                                    uu____37965
                                                                    ::
                                                                    uu____37985
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____37951
                                                                     in
                                                                    uu____37917
                                                                    ::
                                                                    uu____37937
                                                                     in
                                                                    uu____37865
                                                                    ::
                                                                    uu____37903
                                                                     in
                                                                    uu____37831
                                                                    ::
                                                                    uu____37851
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____37817
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____37803
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____37789
                                                                     in
                                                                    uu____37755
                                                                    ::
                                                                    uu____37775
                                                                     in
                                                                    uu____37721
                                                                    ::
                                                                    uu____37741
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____37707
                                                                     in
                                                                    uu____37673
                                                                    ::
                                                                    uu____37693
                                                                     in
                                                                    uu____37639
                                                                    ::
                                                                    uu____37659
                                                                     in
                                                                    uu____37605
                                                                    ::
                                                                    uu____37625
                                                                     in
                                                                    uu____37571
                                                                    ::
                                                                    uu____37591
                                                                     in
                                                                    uu____37537
                                                                    ::
                                                                    uu____37557
                                                                     in
                                                                    uu____37503
                                                                    ::
                                                                    uu____37523
                                                                     in
                                                                    uu____37469
                                                                    ::
                                                                    uu____37489
                                                                     in
                                                                    uu____37435
                                                                    ::
                                                                    uu____37455
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____37421
                                                                     in
                                                                    uu____37387
                                                                    ::
                                                                    uu____37407
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____37373
                                                                     in
                                                                    uu____37339
                                                                    ::
                                                                    uu____37359
                                                                     in
                                                                    uu____37305
                                                                    ::
                                                                    uu____37325
                                                                     in
                                                                    uu____37271
                                                                    ::
                                                                    uu____37291
                                                                     in
                                                                    uu____37237
                                                                    ::
                                                                    uu____37257
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____37223
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____37209
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____37195
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____37181
                                                                     in
                                                                    uu____37147
                                                                    ::
                                                                    uu____37167
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____37133
                                                                     in
                                                                    uu____37099
                                                                    ::
                                                                    uu____37119
                                                                     in
                                                                    uu____37065
                                                                    ::
                                                                    uu____37085
                                                                     in
                                                                    uu____37031
                                                                    ::
                                                                    uu____37051
                                                                     in
                                                                    uu____36997
                                                                    ::
                                                                    uu____37017
                                                                     in
                                                                    uu____36963
                                                                    ::
                                                                    uu____36983
                                                                     in
                                                                    uu____36929
                                                                    ::
                                                                    uu____36949
                                                                     in
                                                                    uu____36895
                                                                    ::
                                                                    uu____36915
                                                                     in
                                                                    uu____36861
                                                                    ::
                                                                    uu____36881
                                                                     in
                                                                    uu____36827
                                                                    ::
                                                                    uu____36847
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____36813
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____36799
                                                                     in
                                                                    uu____36765
                                                                    ::
                                                                    uu____36785
                                                                     in
                                                                    uu____36731
                                                                    ::
                                                                    uu____36751
                                                                     in
                                                                    uu____36697
                                                                    ::
                                                                    uu____36717
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____36683
                                                                     in
                                                                    uu____36649
                                                                    ::
                                                                    uu____36669
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____36635
                                                                     in
                                                                    uu____36601
                                                                    ::
                                                                    uu____36621
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____36587
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____36573
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____36559
                                                                     in
                                                                    uu____36525
                                                                    ::
                                                                    uu____36545
                                                                     in
                                                                    uu____36491
                                                                    ::
                                                                    uu____36511
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____36477
                                                                     in
                                                                    uu____36443
                                                                    ::
                                                                    uu____36463
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    "Retain comments in the logged SMT queries (requires --log_queries; default true)")
                                                                    ::
                                                                    uu____36429
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____36415
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try initially (default 2)")
                                                                    ::
                                                                    uu____36401
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "protect_top_level_axioms",
                                                                    BoolStr,
                                                                    "Guard nullary top-level symbols in the SMT encoding from provide ambient ground facts (default 'true')")
                                                                    ::
                                                                    uu____36387
                                                                     in
                                                                    uu____36353
                                                                    ::
                                                                    uu____36373
                                                                     in
                                                                  uu____36319
                                                                    ::
                                                                    uu____36339
                                                                   in
                                                                uu____36285
                                                                  ::
                                                                  uu____36305
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "include",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "path")),
                                                                "A directory in which to search for files included on the command line")
                                                                ::
                                                                uu____36271
                                                               in
                                                            uu____36237 ::
                                                              uu____36257
                                                             in
                                                          uu____36203 ::
                                                            uu____36223
                                                           in
                                                        uu____36169 ::
                                                          uu____36189
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "hint_file",
                                                        (PathStr "path"),
                                                        "Read/write hints to <path> (instead of module-specific hints files)")
                                                        :: uu____36155
                                                       in
                                                    uu____36121 ::
                                                      uu____36141
                                                     in
                                                  uu____36087 :: uu____36107
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "extract_namespace",
                                                  (Accumulated
                                                     (PostProcessed
                                                        (pp_lowercase,
                                                          (SimpleStr
                                                             "namespace name")))),
                                                  "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                  :: uu____36073
                                                 in
                                              (FStar_Getopt.noshort,
                                                "extract_module",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "module_name")))),
                                                "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                                :: uu____36059
                                               in
                                            (FStar_Getopt.noshort, "extract",
                                              (Accumulated
                                                 (SimpleStr
                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                              "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                              :: uu____36045
                                             in
                                          uu____36011 :: uu____36031  in
                                        uu____35977 :: uu____35997  in
                                      (FStar_Getopt.noshort, "dump_module",
                                        (Accumulated
                                           (SimpleStr "module_name")), "")
                                        :: uu____35963
                                       in
                                    uu____35929 :: uu____35949  in
                                  uu____35895 :: uu____35915  in
                                uu____35861 :: uu____35881  in
                              (FStar_Getopt.noshort, "dep",
                                (EnumStr ["make"; "graph"; "full"; "raw"]),
                                "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                                :: uu____35847
                               in
                            (FStar_Getopt.noshort, "defensive",
                              (EnumStr ["no"; "warn"; "fail"]),
                              "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                              :: uu____35833
                             in
                          (FStar_Getopt.noshort, "debug_level",
                            (Accumulated
                               (OpenEnumStr
                                  (["Low"; "Medium"; "High"; "Extreme"],
                                    "..."))),
                            "Control the verbosity of debugging info") ::
                            uu____35819
                           in
                        (FStar_Getopt.noshort, "debug",
                          (Accumulated (SimpleStr "module_name")),
                          "Print lots of debugging information while checking module")
                          :: uu____35805
                         in
                      (FStar_Getopt.noshort, "codegen-lib",
                        (Accumulated (SimpleStr "namespace")),
                        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                        :: uu____35791
                       in
                    (FStar_Getopt.noshort, "codegen",
                      (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                      "Generate code for further compilation to executable code, or build a compiler plugin")
                      :: uu____35777
                     in
                  uu____35743 :: uu____35763  in
                uu____35709 :: uu____35729  in
              (FStar_Getopt.noshort, "cache_dir",
                (PostProcessed (pp_validate_dir, (PathStr "dir"))),
                "Read and write .checked and .checked.lax in directory <dir>")
                :: uu____35695
               in
            uu____35661 :: uu____35681  in
          (FStar_Getopt.noshort, "already_cached",
            (Accumulated
               (SimpleStr
                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
            "\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")
            :: uu____35647
           in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____35633
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____35619
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___296_39884  ->
             match uu___296_39884 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____35605

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____39913  ->
    let uu____39916 = specs_with_types ()  in
    FStar_List.map
      (fun uu____39947  ->
         match uu____39947 with
         | (short,long,typ,doc) ->
             let uu____39969 =
               let uu____39983 = arg_spec_of_opt_type long typ  in
               (short, long, uu____39983, doc)  in
             mk_spec uu____39969) uu____39916

let (settable : Prims.string -> Prims.bool) =
  fun uu___297_39998  ->
    match uu___297_39998 with
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
    | uu____40121 -> false
  
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
       (fun uu____40220  ->
          match uu____40220 with
          | (uu____40235,x,uu____40237,uu____40238) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____40313  ->
          match uu____40313 with
          | (uu____40328,x,uu____40330,uu____40331) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____40347  ->
    let uu____40348 = specs ()  in display_usage_aux uu____40348
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____40380 -> true
    | uu____40383 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____40393 -> uu____40393
  
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
        (fun uu___759_40414  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____40431 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____40431
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____40456  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____40462 =
             let uu____40466 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____40466 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____40462)
       in
    let uu____40523 =
      let uu____40527 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____40527
       in
    (res, uu____40523)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____40569  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____40612 = specs ()  in
       FStar_Getopt.parse_cmdline uu____40612 (fun x  -> ())  in
     (let uu____40619 =
        let uu____40625 =
          let uu____40626 = FStar_List.map mk_string old_verify_module  in
          List uu____40626  in
        ("verify_module", uu____40625)  in
      set_option' uu____40619);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____40645 =
        let uu____40647 =
          let uu____40649 =
            let uu____40651 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____40651  in
          (FStar_String.length f1) - uu____40649  in
        uu____40647 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____40645  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____40664 = get_lax ()  in
    if uu____40664
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____40685 = module_name_of_file_name fn  in
    should_verify uu____40685
  
let (module_name_eq : Prims.string -> Prims.string -> Prims.bool) =
  fun m1  ->
    fun m2  -> (FStar_String.lowercase m1) = (FStar_String.lowercase m2)
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____40713 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____40713 (FStar_List.existsb (module_name_eq m))
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____40731 = should_verify m  in
    if uu____40731 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____40748  ->
    let cache_dir =
      let uu____40753 = get_cache_dir ()  in
      match uu____40753 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some c -> [c]  in
    let uu____40767 = get_no_default_includes ()  in
    if uu____40767
    then
      let uu____40773 = get_include ()  in
      FStar_List.append cache_dir uu____40773
    else
      (let lib_paths =
         let uu____40784 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____40784 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = FStar_String.op_Hat fstar_bin_directory "/.."
                in
             let defs = universe_include_path_base_dirs  in
             let uu____40800 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> FStar_String.op_Hat fstar_home x))
                in
             FStar_All.pipe_right uu____40800
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____40827 =
         let uu____40831 =
           let uu____40835 = get_include ()  in
           FStar_List.append uu____40835 ["."]  in
         FStar_List.append lib_paths uu____40831  in
       FStar_List.append cache_dir uu____40827)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____40866 = FStar_Util.smap_try_find file_map filename  in
    match uu____40866 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___810_40897  ->
               match () with
               | () ->
                   let uu____40901 = FStar_Util.is_path_absolute filename  in
                   if uu____40901
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____40917 =
                        let uu____40921 = include_path ()  in
                        FStar_List.rev uu____40921  in
                      FStar_Util.find_map uu____40917
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___809_40949 -> FStar_Pervasives_Native.None  in
        (if FStar_Option.isSome result
         then FStar_Util.smap_add file_map filename result
         else ();
         result)
  
let (prims : unit -> Prims.string) =
  fun uu____40968  ->
    let uu____40969 = get_prims ()  in
    match uu____40969 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____40978 = find_file filename  in
        (match uu____40978 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____40987 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____40987)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____41000  ->
    let uu____41001 = prims ()  in FStar_Util.basename uu____41001
  
let (pervasives : unit -> Prims.string) =
  fun uu____41009  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____41013 = find_file filename  in
    match uu____41013 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____41022 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____41022
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____41032  ->
    let uu____41033 = pervasives ()  in FStar_Util.basename uu____41033
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____41041  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____41045 = find_file filename  in
    match uu____41045 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____41054 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____41054
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____41067 = get_odir ()  in
    match uu____41067 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____41085 = get_cache_dir ()  in
    match uu____41085 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____41094 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____41094
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns  ->
    let cache = FStar_Util.smap_create (Prims.parse_int "31")  in
    let with_cache f s =
      let uu____41216 = FStar_Util.smap_try_find cache s  in
      match uu____41216 with
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
             let uu____41351 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____41351  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____41374 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              let s1 = FStar_Util.trim_string s  in
              if s1 = ""
              then []
              else
                with_cache
                  (fun s2  ->
                     let uu____41442 =
                       FStar_All.pipe_right (FStar_Util.splitlines s2)
                         (FStar_List.concatMap
                            (fun s3  -> FStar_Util.split s3 " "))
                        in
                     FStar_All.pipe_right uu____41442
                       (FStar_List.map parse_one_setting)) s1))
       in
    FStar_All.pipe_right uu____41374 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____41517 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____41517 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____41532  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____41541  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____41550  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____41557  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____41564  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____41571  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____41581 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____41592 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____41603 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____41614 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____41623  ->
    let uu____41624 = get_codegen ()  in
    FStar_Util.map_opt uu____41624
      (fun uu___298_41630  ->
         match uu___298_41630 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____41636 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____41649  ->
    let uu____41650 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____41650
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____41676  -> let uu____41677 = get_debug ()  in uu____41677 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____41694 = get_debug ()  in
    FStar_All.pipe_right uu____41694
      (FStar_List.existsb (module_name_eq modul))
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____41719 = get_debug ()  in
       FStar_All.pipe_right uu____41719
         (FStar_List.existsb (module_name_eq modul)))
        && (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____41734  ->
    let uu____41735 = get_defensive ()  in uu____41735 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____41745  ->
    let uu____41746 = get_defensive ()  in uu____41746 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____41758  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____41765  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____41772  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____41779  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____41789 = get_dump_module ()  in
    FStar_All.pipe_right uu____41789 (FStar_List.existsb (module_name_eq s))
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____41804  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____41811  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____41821 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____41821
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____41857  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____41865  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____41872  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____41881  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____41888  -> get_ide () 
let (print : unit -> Prims.bool) = fun uu____41895  -> get_print () 
let (print_in_place : unit -> Prims.bool) =
  fun uu____41902  -> get_print_in_place () 
let profile : 'a . (unit -> 'a) -> ('a -> Prims.string) -> 'a =
  fun f  ->
    fun msg  ->
      let uu____41933 = get_profile ()  in
      if uu____41933
      then
        let uu____41936 = FStar_Util.record_time f  in
        match uu____41936 with
        | (a,time) ->
            ((let uu____41947 = FStar_Util.string_of_int time  in
              let uu____41949 = msg a  in
              FStar_Util.print2 "Elapsed time %s ms: %s\n" uu____41947
                uu____41949);
             a)
      else f ()
  
let (protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____41960  -> get_protect_top_level_axioms () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____41967  ->
    let uu____41968 = get_initial_fuel ()  in
    let uu____41970 = get_max_fuel ()  in Prims.min uu____41968 uu____41970
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____41978  ->
    let uu____41979 = get_initial_ifuel ()  in
    let uu____41981 = get_max_ifuel ()  in Prims.min uu____41979 uu____41981
  
let (interactive : unit -> Prims.bool) =
  fun uu____41989  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____41996  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____42005  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____42012  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____42019  -> get_log_queries () 
let (keep_query_captions : unit -> Prims.bool) =
  fun uu____42026  -> (log_queries ()) && (get_keep_query_captions ()) 
let (log_types : unit -> Prims.bool) = fun uu____42033  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____42040  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____42047  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____42054  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____42061  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____42067  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____42076  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____42083  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____42093 = get_no_extract ()  in
    FStar_All.pipe_right uu____42093 (FStar_List.existsb (module_name_eq s))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____42108  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____42115  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____42122  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____42129  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____42138  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____42145  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____42152  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____42159  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____42166  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____42173  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____42180  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____42187  -> get_print_z3_statistics () 
let (query_stats : unit -> Prims.bool) =
  fun uu____42194  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____42201  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____42210  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____42217  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____42224  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____42231  ->
    let uu____42232 = get_smtencoding_nl_arith_repr ()  in
    uu____42232 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____42242  ->
    let uu____42243 = get_smtencoding_nl_arith_repr ()  in
    uu____42243 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____42253  ->
    let uu____42254 = get_smtencoding_nl_arith_repr ()  in
    uu____42254 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____42264  ->
    let uu____42265 = get_smtencoding_l_arith_repr ()  in
    uu____42265 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____42275  ->
    let uu____42276 = get_smtencoding_l_arith_repr ()  in
    uu____42276 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____42286  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____42293  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____42300  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____42307  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____42314  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____42321  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____42328  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____42335  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____42342  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____42349  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____42356  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____42363  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____42370  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____42377  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____42386  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____42393  -> get_use_tactics () 
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu____42409  ->
    let uu____42410 = get_using_facts_from ()  in
    match uu____42410 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____42464  ->
    let uu____42465 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____42465
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____42476  ->
    let uu____42477 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____42477 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____42485 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____42496  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____42503  ->
    let uu____42504 = get_smt ()  in
    match uu____42504 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____42522  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____42529  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____42536  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____42543  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____42550  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____42557  ->
    (get_use_two_phase_tc ()) &&
      (let uu____42559 = lax ()  in Prims.op_Negation uu____42559)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____42567  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____42574  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____42581  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____42588  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____42595  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____42612 =
      let uu____42614 = trace_error ()  in Prims.op_Negation uu____42614  in
    if uu____42612
    then
      (push ();
       (let r =
          try
            (fun uu___1007_42629  ->
               match () with
               | () -> let uu____42634 = f ()  in FStar_Util.Inr uu____42634)
              ()
          with | uu___1006_42636 -> FStar_Util.Inl uu___1006_42636  in
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
        | (uu____42717,[]) -> true
        | (m2::ms,p::ps) ->
            (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
        | uu____42750 -> false  in
      let uu____42762 =
        FStar_All.pipe_right setting
          (FStar_Util.try_find
             (fun uu____42804  ->
                match uu____42804 with
                | (path,uu____42815) -> matches_path m_components path))
         in
      match uu____42762 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____42834,flag) -> flag
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____42863 = get_extract ()  in
    match uu____42863 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____42878 =
            let uu____42894 = get_no_extract ()  in
            let uu____42898 = get_extract_namespace ()  in
            let uu____42902 = get_extract_module ()  in
            (uu____42894, uu____42898, uu____42902)  in
          match uu____42878 with
          | ([],[],[]) -> ()
          | uu____42927 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         module_matches_namespace_filter m1 extract_setting)
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____42956 = get_extract_namespace ()  in
          match uu____42956 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____42984 = get_extract_module ()  in
          match uu____42984 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____43006 = no_extract m1  in Prims.op_Negation uu____43006)
          &&
          (let uu____43009 =
             let uu____43020 = get_extract_namespace ()  in
             let uu____43024 = get_extract_module ()  in
             (uu____43020, uu____43024)  in
           (match uu____43009 with
            | ([],[]) -> true
            | uu____43044 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  
let (should_be_already_cached : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____43064 = get_already_cached ()  in
    match uu____43064 with
    | FStar_Pervasives_Native.None  -> false
    | FStar_Pervasives_Native.Some already_cached_setting ->
        module_matches_namespace_filter m already_cached_setting
  
let (error_flags : unit -> error_flag Prims.list) =
  let cache = FStar_Util.smap_create (Prims.parse_int "10")  in
  fun uu____43097  ->
    let we = warn_error ()  in
    let uu____43100 = FStar_Util.smap_try_find cache we  in
    match uu____43100 with
    | FStar_Pervasives_Native.None  ->
        let r = parse_warn_error we  in (FStar_Util.smap_add cache we r; r)
    | FStar_Pervasives_Native.Some r -> r
  