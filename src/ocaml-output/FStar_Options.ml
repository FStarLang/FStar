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
    match projectee with | Low  -> true | uu____34741 -> false
  
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____34752 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | High  -> true | uu____34763 -> false
  
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____34774 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____34787 -> false
  
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
    match projectee with | Bool _0 -> true | uu____34842 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____34866 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____34890 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____34914 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____34939 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____34964 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _34972  -> Bool _34972 
let (mk_string : Prims.string -> option_val) = fun _34979  -> String _34979 
let (mk_path : Prims.string -> option_val) = fun _34986  -> Path _34986 
let (mk_int : Prims.int -> option_val) = fun _34993  -> Int _34993 
let (mk_list : option_val Prims.list -> option_val) =
  fun _35001  -> List _35001 
type options =
  | Set 
  | Reset 
  | Restore 
let (uu___is_Set : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Set  -> true | uu____35011 -> false
  
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____35022 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____35033 -> false
  
type error_flag =
  | CFatal 
  | CAlwaysError 
  | CError 
  | CWarning 
  | CSilent 
let (uu___is_CFatal : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CFatal  -> true | uu____35044 -> false
  
let (uu___is_CAlwaysError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CAlwaysError  -> true | uu____35055 -> false
  
let (uu___is_CError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CError  -> true | uu____35066 -> false
  
let (uu___is_CWarning : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CWarning  -> true | uu____35077 -> false
  
let (uu___is_CSilent : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CSilent  -> true | uu____35088 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____35113  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____35140  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____35168  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___289_35197  ->
    match uu___289_35197 with
    | Bool b -> b
    | uu____35201 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___290_35210  ->
    match uu___290_35210 with
    | Int b -> b
    | uu____35214 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___291_35223  ->
    match uu___291_35223 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____35229 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___292_35239  ->
    match uu___292_35239 with
    | List ts -> ts
    | uu____35245 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____35256 .
    (option_val -> 'Auu____35256) -> option_val -> 'Auu____35256 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____35274 = as_list' x  in
      FStar_All.pipe_right uu____35274 (FStar_List.map as_t)
  
let as_option :
  'Auu____35288 .
    (option_val -> 'Auu____35288) ->
      option_val -> 'Auu____35288 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___293_35303  ->
      match uu___293_35303 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____35307 = as_t v1  in
          FStar_Pervasives_Native.Some uu____35307
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___294_35316  ->
    match uu___294_35316 with
    | List ls ->
        let uu____35323 =
          FStar_List.map
            (fun l  ->
               let uu____35335 = as_string l  in
               FStar_Util.split uu____35335 ",") ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____35323
    | uu____35347 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let copy_optionstate :
  'Auu____35359 .
    'Auu____35359 FStar_Util.smap -> 'Auu____35359 FStar_Util.smap
  = fun m  -> FStar_Util.smap_copy m 
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (internal_peek : unit -> optionstate) =
  fun uu____35400  ->
    let uu____35401 =
      let uu____35404 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____35404  in
    FStar_List.hd uu____35401
  
let (peek : unit -> optionstate) = fun uu____35443  -> internal_peek () 
let (pop : unit -> unit) =
  fun uu____35449  ->
    let uu____35450 = FStar_ST.op_Bang fstar_options  in
    match uu____35450 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____35485::[] -> failwith "TOO MANY POPS!"
    | uu____35493::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____35535  ->
    let uu____35536 =
      let uu____35541 =
        let uu____35544 =
          let uu____35547 = FStar_ST.op_Bang fstar_options  in
          FStar_List.hd uu____35547  in
        FStar_List.map copy_optionstate uu____35544  in
      let uu____35581 = FStar_ST.op_Bang fstar_options  in uu____35541 ::
        uu____35581
       in
    FStar_ST.op_Colon_Equals fstar_options uu____35536
  
let (internal_pop : unit -> Prims.bool) =
  fun uu____35648  ->
    let curstack =
      let uu____35652 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____35652  in
    match curstack with
    | [] -> failwith "impossible: empty current option stack"
    | uu____35689::[] -> false
    | uu____35691::tl1 ->
        ((let uu____35696 =
            let uu____35701 =
              let uu____35706 = FStar_ST.op_Bang fstar_options  in
              FStar_List.tl uu____35706  in
            tl1 :: uu____35701  in
          FStar_ST.op_Colon_Equals fstar_options uu____35696);
         true)
  
let (internal_push : unit -> unit) =
  fun uu____35775  ->
    let curstack =
      let uu____35779 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____35779  in
    let stack' =
      let uu____35816 =
        let uu____35817 = FStar_List.hd curstack  in
        copy_optionstate uu____35817  in
      uu____35816 :: curstack  in
    let uu____35820 =
      let uu____35825 =
        let uu____35830 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____35830  in
      stack' :: uu____35825  in
    FStar_ST.op_Colon_Equals fstar_options uu____35820
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____35899 = FStar_ST.op_Bang fstar_options  in
    match uu____35899 with
    | [] -> failwith "set on empty option stack"
    | []::uu____35934 -> failwith "set on empty current option stack"
    | (uu____35942::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
  
let (snapshot : unit -> (Prims.int * unit)) =
  fun uu____35992  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____36022 = peek ()  in FStar_Util.smap_add uu____36022 k v1
  
let (set_option' : (Prims.string * option_val) -> unit) =
  fun uu____36035  -> match uu____36035 with | (k,v1) -> set_option k v1 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____36074 =
      let uu____36078 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____36078
       in
    FStar_ST.op_Colon_Equals light_off_files uu____36074
  
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
    let uu____37048 = FStar_ST.op_Bang r  in
    match uu____37048 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some f)
    | uu____37183 -> failwith "Multiple initialization of FStar.Options"  in
  let get1 uu____37204 =
    let uu____37205 = FStar_ST.op_Bang r  in
    match uu____37205 with
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
    let uu____37366 = FStar_Pervasives_Native.snd parse_warn_error_set_get ()
       in
    uu____37366 s
  
let (init : unit -> unit) =
  fun uu____37397  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____37417  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____37490 =
      let uu____37493 = peek ()  in FStar_Util.smap_try_find uu____37493 s
       in
    match uu____37490 with
    | FStar_Pervasives_Native.None  ->
        let uu____37496 =
          let uu____37498 = FStar_String.op_Hat s " not found"  in
          FStar_String.op_Hat "Impossible: option " uu____37498  in
        failwith uu____37496
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____37510 .
    Prims.string -> (option_val -> 'Auu____37510) -> 'Auu____37510
  = fun s  -> fun c  -> let uu____37528 = get_option s  in c uu____37528 
let (get_abort_on : unit -> Prims.int) =
  fun uu____37535  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____37544  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____37555  -> lookup_opt "admit_except" (as_option as_string) 
let (get_already_cached :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____37571  ->
    lookup_opt "already_cached" (as_option (as_list as_string))
  
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____37588  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37599  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____37611  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____37620  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37631  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____37645  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____37659  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____37673  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____37684  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37695  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____37707  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____37716  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____37725  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____37736  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____37748  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____37757  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____37770  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____37789  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____37803  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____37815  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____37824  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____37833  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____37844  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____37856  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____37865  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____37876  -> lookup_opt "include" (as_list as_string) 
let (get_print : unit -> Prims.bool) =
  fun uu____37888  -> lookup_opt "print" as_bool 
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____37897  -> lookup_opt "print_in_place" as_bool 
let (get_profile : unit -> Prims.bool) =
  fun uu____37906  -> lookup_opt "profile" as_bool 
let (get_protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____37915  -> lookup_opt "protect_top_level_axioms" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____37924  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____37933  -> lookup_opt "initial_ifuel" as_int 
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu____37942  -> lookup_opt "keep_query_captions" as_bool 
let (get_lax : unit -> Prims.bool) =
  fun uu____37951  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____37962  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____37974  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____37983  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____37992  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____38001  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____38010  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____38019  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____38028  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____38037  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____38048  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____38060  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____38069  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____38078  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____38087  ->
    lookup_opt "normalize_pure_terms_for_extraction" as_bool
  
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38098  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____38110  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38121  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____38133  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____38142  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____38151  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____38160  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____38169  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____38178  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____38187  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____38196  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____38205  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38216  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____38228  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38239  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____38251  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____38260  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____38269  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____38278  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____38287  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____38296  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____38305  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____38314  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____38323  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____38332  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____38341  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____38350  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____38359  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____38368  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____38377  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____38386  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____38395  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38406  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____38418  ->
    let uu____38419 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____38419
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____38433  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____38452  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____38466  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____38480  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____38492  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____38501  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____38512  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____38524  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____38533  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____38542  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____38551  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____38560  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____38569  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____38578  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____38587  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____38596  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____38605  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___295_38614  ->
    match uu___295_38614 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____38635 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____38644 = get_debug_level ()  in
    FStar_All.pipe_right uu____38644
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "<not set>" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____38810  ->
    let uu____38811 =
      let uu____38813 = FStar_ST.op_Bang _version  in
      let uu____38836 = FStar_ST.op_Bang _platform  in
      let uu____38859 = FStar_ST.op_Bang _compiler  in
      let uu____38882 = FStar_ST.op_Bang _date  in
      let uu____38905 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____38813
        uu____38836 uu____38859 uu____38882 uu____38905
       in
    FStar_Util.print_string uu____38811
  
let display_usage_aux :
  'Auu____38936 'Auu____38937 .
    ('Auu____38936 * Prims.string * 'Auu____38937 FStar_Getopt.opt_variant *
      Prims.string) Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____38992  ->
         match uu____38992 with
         | (uu____39005,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____39024 =
                      let uu____39026 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____39026  in
                    FStar_Util.print_string uu____39024
                  else
                    (let uu____39031 =
                       let uu____39033 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____39033 doc  in
                     FStar_Util.print_string uu____39031)
              | FStar_Getopt.OneArg (uu____39036,argname) ->
                  if doc = ""
                  then
                    let uu____39051 =
                      let uu____39053 = FStar_Util.colorize_bold flag  in
                      let uu____39055 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____39053
                        uu____39055
                       in
                    FStar_Util.print_string uu____39051
                  else
                    (let uu____39060 =
                       let uu____39062 = FStar_Util.colorize_bold flag  in
                       let uu____39064 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____39062
                         uu____39064 doc
                        in
                     FStar_Util.print_string uu____39060))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____39099 = o  in
    match uu____39099 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____39141 =
                let uu____39142 = f ()  in set_option name uu____39142  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____39163 = f x  in set_option name uu____39163
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____39190 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____39190  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____39216 =
        let uu____39219 = lookup_opt name as_list'  in
        FStar_List.append uu____39219 [value]  in
      mk_list uu____39216
  
let accumulate_string :
  'Auu____39233 .
    Prims.string -> ('Auu____39233 -> Prims.string) -> 'Auu____39233 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____39258 =
          let uu____39259 =
            let uu____39260 = post_processor value  in mk_string uu____39260
             in
          accumulated_option name uu____39259  in
        set_option name uu____39258
  
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
    match projectee with | Const _0 -> true | uu____39382 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____39403 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____39425 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____39438 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____39462 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____39488 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____39525 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____39576 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____39617 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____39637 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____39664 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____39708 -> true
    | uu____39711 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____39722 -> uu____39722
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___581_39746  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____39748 ->
                      let uu____39750 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____39750 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____39758 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____39758
                  | PathStr uu____39775 -> mk_path str_val
                  | SimpleStr uu____39777 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____39787 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____39804 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____39804
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
            let uu____39824 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____39824
  
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ  ->
    let desc_of_enum cases =
      let uu____39854 =
        let uu____39856 =
          FStar_String.op_Hat (FStar_String.concat "|" cases) "]"  in
        FStar_String.op_Hat "[" uu____39856  in
      FStar_Pervasives_Native.Some uu____39854  in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____39898,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____39908,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____39939 = desc_of_opt_type typ  in
      match uu____39939 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____39947  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____39973 =
      let uu____39975 = as_string s  in FStar_String.lowercase uu____39975
       in
    mk_string uu____39973
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string)
      Prims.list)
  =
  fun uu____40032  ->
    let uu____40046 =
      let uu____40060 =
        let uu____40074 =
          let uu____40088 =
            let uu____40102 =
              let uu____40114 =
                let uu____40115 = mk_bool true  in Const uu____40115  in
              (FStar_Getopt.noshort, "cache_checked_modules", uu____40114,
                "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
               in
            let uu____40122 =
              let uu____40136 =
                let uu____40150 =
                  let uu____40162 =
                    let uu____40163 = mk_bool true  in Const uu____40163  in
                  (FStar_Getopt.noshort, "cache_off", uu____40162,
                    "Do not read or write any .checked files")
                   in
                let uu____40170 =
                  let uu____40184 =
                    let uu____40196 =
                      let uu____40197 = mk_bool true  in Const uu____40197
                       in
                    (FStar_Getopt.noshort, "cmi", uu____40196,
                      "Inline across module interfaces during extraction (aka. cross-module inlining)")
                     in
                  let uu____40204 =
                    let uu____40218 =
                      let uu____40232 =
                        let uu____40246 =
                          let uu____40260 =
                            let uu____40274 =
                              let uu____40288 =
                                let uu____40302 =
                                  let uu____40314 =
                                    let uu____40315 = mk_bool true  in
                                    Const uu____40315  in
                                  (FStar_Getopt.noshort, "detail_errors",
                                    uu____40314,
                                    "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                   in
                                let uu____40322 =
                                  let uu____40336 =
                                    let uu____40348 =
                                      let uu____40349 = mk_bool true  in
                                      Const uu____40349  in
                                    (FStar_Getopt.noshort,
                                      "detail_hint_replay", uu____40348,
                                      "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                     in
                                  let uu____40356 =
                                    let uu____40370 =
                                      let uu____40382 =
                                        let uu____40383 = mk_bool true  in
                                        Const uu____40383  in
                                      (FStar_Getopt.noshort, "doc",
                                        uu____40382,
                                        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                       in
                                    let uu____40390 =
                                      let uu____40404 =
                                        let uu____40418 =
                                          let uu____40430 =
                                            let uu____40431 = mk_bool true
                                               in
                                            Const uu____40431  in
                                          (FStar_Getopt.noshort,
                                            "eager_inference", uu____40430,
                                            "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                           in
                                        let uu____40438 =
                                          let uu____40452 =
                                            let uu____40464 =
                                              let uu____40465 = mk_bool true
                                                 in
                                              Const uu____40465  in
                                            (FStar_Getopt.noshort,
                                              "eager_subtyping", uu____40464,
                                              "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                             in
                                          let uu____40472 =
                                            let uu____40486 =
                                              let uu____40500 =
                                                let uu____40514 =
                                                  let uu____40528 =
                                                    let uu____40540 =
                                                      let uu____40541 =
                                                        mk_bool true  in
                                                      Const uu____40541  in
                                                    (FStar_Getopt.noshort,
                                                      "expose_interfaces",
                                                      uu____40540,
                                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                     in
                                                  let uu____40548 =
                                                    let uu____40562 =
                                                      let uu____40574 =
                                                        let uu____40575 =
                                                          mk_bool true  in
                                                        Const uu____40575  in
                                                      (FStar_Getopt.noshort,
                                                        "hide_uvar_nums",
                                                        uu____40574,
                                                        "Don't print unification variable numbers")
                                                       in
                                                    let uu____40582 =
                                                      let uu____40596 =
                                                        let uu____40610 =
                                                          let uu____40622 =
                                                            let uu____40623 =
                                                              mk_bool true
                                                               in
                                                            Const uu____40623
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "hint_info",
                                                            uu____40622,
                                                            "Print information regarding hints (deprecated; use --query_stats instead)")
                                                           in
                                                        let uu____40630 =
                                                          let uu____40644 =
                                                            let uu____40656 =
                                                              let uu____40657
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____40657
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "in",
                                                              uu____40656,
                                                              "Legacy interactive mode; reads input from stdin")
                                                             in
                                                          let uu____40664 =
                                                            let uu____40678 =
                                                              let uu____40690
                                                                =
                                                                let uu____40691
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____40691
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "ide",
                                                                uu____40690,
                                                                "JSON-based interactive mode for IDEs")
                                                               in
                                                            let uu____40698 =
                                                              let uu____40712
                                                                =
                                                                let uu____40726
                                                                  =
                                                                  let uu____40738
                                                                    =
                                                                    let uu____40739
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40739
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "print",
                                                                    uu____40738,
                                                                    "Parses and prettyprints the files included on the command line")
                                                                   in
                                                                let uu____40746
                                                                  =
                                                                  let uu____40760
                                                                    =
                                                                    let uu____40772
                                                                    =
                                                                    let uu____40773
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40773
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_in_place",
                                                                    uu____40772,
                                                                    "Parses and prettyprints in place the files included on the command line")
                                                                     in
                                                                  let uu____40780
                                                                    =
                                                                    let uu____40794
                                                                    =
                                                                    let uu____40806
                                                                    =
                                                                    let uu____40807
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40807
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "profile",
                                                                    uu____40806,
                                                                    "Prints timing information for various operations in the compiler")
                                                                     in
                                                                    let uu____40814
                                                                    =
                                                                    let uu____40828
                                                                    =
                                                                    let uu____40842
                                                                    =
                                                                    let uu____40856
                                                                    =
                                                                    let uu____40870
                                                                    =
                                                                    let uu____40884
                                                                    =
                                                                    let uu____40896
                                                                    =
                                                                    let uu____40897
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40897
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____40896,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____40904
                                                                    =
                                                                    let uu____40918
                                                                    =
                                                                    let uu____40932
                                                                    =
                                                                    let uu____40944
                                                                    =
                                                                    let uu____40945
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40945
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____40944,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____40952
                                                                    =
                                                                    let uu____40966
                                                                    =
                                                                    let uu____40978
                                                                    =
                                                                    let uu____40979
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____40979
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____40978,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____40986
                                                                    =
                                                                    let uu____41000
                                                                    =
                                                                    let uu____41014
                                                                    =
                                                                    let uu____41028
                                                                    =
                                                                    let uu____41042
                                                                    =
                                                                    let uu____41054
                                                                    =
                                                                    let uu____41055
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41055
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____41054,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____41062
                                                                    =
                                                                    let uu____41076
                                                                    =
                                                                    let uu____41090
                                                                    =
                                                                    let uu____41102
                                                                    =
                                                                    let uu____41103
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41103
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____41102,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____41110
                                                                    =
                                                                    let uu____41124
                                                                    =
                                                                    let uu____41138
                                                                    =
                                                                    let uu____41150
                                                                    =
                                                                    let uu____41151
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41151
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____41150,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____41158
                                                                    =
                                                                    let uu____41172
                                                                    =
                                                                    let uu____41184
                                                                    =
                                                                    let uu____41185
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41185
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____41184,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____41192
                                                                    =
                                                                    let uu____41206
                                                                    =
                                                                    let uu____41218
                                                                    =
                                                                    let uu____41219
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41219
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____41218,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____41226
                                                                    =
                                                                    let uu____41240
                                                                    =
                                                                    let uu____41254
                                                                    =
                                                                    let uu____41268
                                                                    =
                                                                    let uu____41280
                                                                    =
                                                                    let uu____41281
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41281
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____41280,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____41288
                                                                    =
                                                                    let uu____41302
                                                                    =
                                                                    let uu____41314
                                                                    =
                                                                    let uu____41315
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41315
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____41314,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____41322
                                                                    =
                                                                    let uu____41336
                                                                    =
                                                                    let uu____41348
                                                                    =
                                                                    let uu____41349
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41349
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____41348,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____41356
                                                                    =
                                                                    let uu____41370
                                                                    =
                                                                    let uu____41382
                                                                    =
                                                                    let uu____41383
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41383
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____41382,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____41390
                                                                    =
                                                                    let uu____41404
                                                                    =
                                                                    let uu____41416
                                                                    =
                                                                    let uu____41417
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41417
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____41416,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____41424
                                                                    =
                                                                    let uu____41438
                                                                    =
                                                                    let uu____41450
                                                                    =
                                                                    let uu____41451
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41451
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____41450,
                                                                    "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)")
                                                                     in
                                                                    let uu____41458
                                                                    =
                                                                    let uu____41472
                                                                    =
                                                                    let uu____41484
                                                                    =
                                                                    let uu____41485
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41485
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____41484,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____41492
                                                                    =
                                                                    let uu____41506
                                                                    =
                                                                    let uu____41518
                                                                    =
                                                                    let uu____41519
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41519
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____41518,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____41526
                                                                    =
                                                                    let uu____41540
                                                                    =
                                                                    let uu____41552
                                                                    =
                                                                    let uu____41553
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41553
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____41552,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____41560
                                                                    =
                                                                    let uu____41574
                                                                    =
                                                                    let uu____41588
                                                                    =
                                                                    let uu____41600
                                                                    =
                                                                    let uu____41601
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41601
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____41600,
                                                                    "Disable all non-critical output")
                                                                     in
                                                                    let uu____41608
                                                                    =
                                                                    let uu____41622
                                                                    =
                                                                    let uu____41636
                                                                    =
                                                                    let uu____41650
                                                                    =
                                                                    let uu____41664
                                                                    =
                                                                    let uu____41678
                                                                    =
                                                                    let uu____41690
                                                                    =
                                                                    let uu____41691
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41691
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____41690,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____41698
                                                                    =
                                                                    let uu____41712
                                                                    =
                                                                    let uu____41724
                                                                    =
                                                                    let uu____41725
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41725
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____41724,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____41732
                                                                    =
                                                                    let uu____41746
                                                                    =
                                                                    let uu____41758
                                                                    =
                                                                    let uu____41759
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41759
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____41758,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____41766
                                                                    =
                                                                    let uu____41780
                                                                    =
                                                                    let uu____41792
                                                                    =
                                                                    let uu____41793
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41793
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____41792,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____41800
                                                                    =
                                                                    let uu____41814
                                                                    =
                                                                    let uu____41828
                                                                    =
                                                                    let uu____41840
                                                                    =
                                                                    let uu____41841
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41841
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____41840,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____41848
                                                                    =
                                                                    let uu____41862
                                                                    =
                                                                    let uu____41876
                                                                    =
                                                                    let uu____41888
                                                                    =
                                                                    let uu____41889
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41889
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____41888,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____41896
                                                                    =
                                                                    let uu____41910
                                                                    =
                                                                    let uu____41922
                                                                    =
                                                                    let uu____41923
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41923
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____41922,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____41930
                                                                    =
                                                                    let uu____41944
                                                                    =
                                                                    let uu____41956
                                                                    =
                                                                    let uu____41957
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41957
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____41956,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____41964
                                                                    =
                                                                    let uu____41978
                                                                    =
                                                                    let uu____41990
                                                                    =
                                                                    let uu____41991
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____41991
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____41990,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____41998
                                                                    =
                                                                    let uu____42012
                                                                    =
                                                                    let uu____42024
                                                                    =
                                                                    let uu____42025
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42025
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____42024,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____42032
                                                                    =
                                                                    let uu____42046
                                                                    =
                                                                    let uu____42058
                                                                    =
                                                                    let uu____42059
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42059
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____42058,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____42066
                                                                    =
                                                                    let uu____42080
                                                                    =
                                                                    let uu____42092
                                                                    =
                                                                    let uu____42093
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42093
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____42092,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____42100
                                                                    =
                                                                    let uu____42114
                                                                    =
                                                                    let uu____42126
                                                                    =
                                                                    let uu____42127
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42127
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____42126,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____42134
                                                                    =
                                                                    let uu____42148
                                                                    =
                                                                    let uu____42162
                                                                    =
                                                                    let uu____42174
                                                                    =
                                                                    let uu____42175
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42175
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____42174,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____42182
                                                                    =
                                                                    let uu____42196
                                                                    =
                                                                    let uu____42208
                                                                    =
                                                                    let uu____42209
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42209
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____42208,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____42216
                                                                    =
                                                                    let uu____42230
                                                                    =
                                                                    let uu____42244
                                                                    =
                                                                    let uu____42258
                                                                    =
                                                                    let uu____42272
                                                                    =
                                                                    let uu____42284
                                                                    =
                                                                    let uu____42285
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42285
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____42284,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____42292
                                                                    =
                                                                    let uu____42306
                                                                    =
                                                                    let uu____42318
                                                                    =
                                                                    let uu____42319
                                                                    =
                                                                    let uu____42327
                                                                    =
                                                                    let uu____42328
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42328
                                                                     in
                                                                    ((fun
                                                                    uu____42335
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____42327)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42319
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____42318,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____42344
                                                                    =
                                                                    let uu____42358
                                                                    =
                                                                    let uu____42370
                                                                    =
                                                                    let uu____42371
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42371
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____42370,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____42378
                                                                    =
                                                                    let uu____42392
                                                                    =
                                                                    let uu____42406
                                                                    =
                                                                    let uu____42418
                                                                    =
                                                                    let uu____42419
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42419
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____42418,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____42426
                                                                    =
                                                                    let uu____42440
                                                                    =
                                                                    let uu____42454
                                                                    =
                                                                    let uu____42468
                                                                    =
                                                                    let uu____42482
                                                                    =
                                                                    let uu____42496
                                                                    =
                                                                    let uu____42508
                                                                    =
                                                                    let uu____42509
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42509
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____42508,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____42516
                                                                    =
                                                                    let uu____42530
                                                                    =
                                                                    let uu____42542
                                                                    =
                                                                    let uu____42543
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42543
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____42542,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____42550
                                                                    =
                                                                    let uu____42564
                                                                    =
                                                                    let uu____42578
                                                                    =
                                                                    let uu____42592
                                                                    =
                                                                    let uu____42606
                                                                    =
                                                                    let uu____42618
                                                                    =
                                                                    let uu____42619
                                                                    =
                                                                    let uu____42627
                                                                    =
                                                                    let uu____42628
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42628
                                                                     in
                                                                    ((fun
                                                                    uu____42634
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____42627)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42619
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____42618,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____42662
                                                                    =
                                                                    let uu____42676
                                                                    =
                                                                    let uu____42688
                                                                    =
                                                                    let uu____42689
                                                                    =
                                                                    let uu____42697
                                                                    =
                                                                    let uu____42698
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42698
                                                                     in
                                                                    ((fun
                                                                    uu____42704
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____42697)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42689
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____42688,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____42732
                                                                    =
                                                                    let uu____42746
                                                                    =
                                                                    let uu____42758
                                                                    =
                                                                    let uu____42759
                                                                    =
                                                                    let uu____42767
                                                                    =
                                                                    let uu____42768
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____42768
                                                                     in
                                                                    ((fun
                                                                    uu____42775
                                                                     ->
                                                                    (
                                                                    let uu____42777
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____42777);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____42767)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____42759
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____42758,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____42746]
                                                                     in
                                                                    uu____42676
                                                                    ::
                                                                    uu____42732
                                                                     in
                                                                    uu____42606
                                                                    ::
                                                                    uu____42662
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____42592
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____42578
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____42564
                                                                     in
                                                                    uu____42530
                                                                    ::
                                                                    uu____42550
                                                                     in
                                                                    uu____42496
                                                                    ::
                                                                    uu____42516
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____42482
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____42468
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____42454
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____42440
                                                                     in
                                                                    uu____42406
                                                                    ::
                                                                    uu____42426
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____42392
                                                                     in
                                                                    uu____42358
                                                                    ::
                                                                    uu____42378
                                                                     in
                                                                    uu____42306
                                                                    ::
                                                                    uu____42344
                                                                     in
                                                                    uu____42272
                                                                    ::
                                                                    uu____42292
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____42258
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____42244
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____42230
                                                                     in
                                                                    uu____42196
                                                                    ::
                                                                    uu____42216
                                                                     in
                                                                    uu____42162
                                                                    ::
                                                                    uu____42182
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____42148
                                                                     in
                                                                    uu____42114
                                                                    ::
                                                                    uu____42134
                                                                     in
                                                                    uu____42080
                                                                    ::
                                                                    uu____42100
                                                                     in
                                                                    uu____42046
                                                                    ::
                                                                    uu____42066
                                                                     in
                                                                    uu____42012
                                                                    ::
                                                                    uu____42032
                                                                     in
                                                                    uu____41978
                                                                    ::
                                                                    uu____41998
                                                                     in
                                                                    uu____41944
                                                                    ::
                                                                    uu____41964
                                                                     in
                                                                    uu____41910
                                                                    ::
                                                                    uu____41930
                                                                     in
                                                                    uu____41876
                                                                    ::
                                                                    uu____41896
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____41862
                                                                     in
                                                                    uu____41828
                                                                    ::
                                                                    uu____41848
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____41814
                                                                     in
                                                                    uu____41780
                                                                    ::
                                                                    uu____41800
                                                                     in
                                                                    uu____41746
                                                                    ::
                                                                    uu____41766
                                                                     in
                                                                    uu____41712
                                                                    ::
                                                                    uu____41732
                                                                     in
                                                                    uu____41678
                                                                    ::
                                                                    uu____41698
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____41664
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____41650
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____41636
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____41622
                                                                     in
                                                                    uu____41588
                                                                    ::
                                                                    uu____41608
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____41574
                                                                     in
                                                                    uu____41540
                                                                    ::
                                                                    uu____41560
                                                                     in
                                                                    uu____41506
                                                                    ::
                                                                    uu____41526
                                                                     in
                                                                    uu____41472
                                                                    ::
                                                                    uu____41492
                                                                     in
                                                                    uu____41438
                                                                    ::
                                                                    uu____41458
                                                                     in
                                                                    uu____41404
                                                                    ::
                                                                    uu____41424
                                                                     in
                                                                    uu____41370
                                                                    ::
                                                                    uu____41390
                                                                     in
                                                                    uu____41336
                                                                    ::
                                                                    uu____41356
                                                                     in
                                                                    uu____41302
                                                                    ::
                                                                    uu____41322
                                                                     in
                                                                    uu____41268
                                                                    ::
                                                                    uu____41288
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____41254
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____41240
                                                                     in
                                                                    uu____41206
                                                                    ::
                                                                    uu____41226
                                                                     in
                                                                    uu____41172
                                                                    ::
                                                                    uu____41192
                                                                     in
                                                                    uu____41138
                                                                    ::
                                                                    uu____41158
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____41124
                                                                     in
                                                                    uu____41090
                                                                    ::
                                                                    uu____41110
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____41076
                                                                     in
                                                                    uu____41042
                                                                    ::
                                                                    uu____41062
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____41028
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____41014
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____41000
                                                                     in
                                                                    uu____40966
                                                                    ::
                                                                    uu____40986
                                                                     in
                                                                    uu____40932
                                                                    ::
                                                                    uu____40952
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____40918
                                                                     in
                                                                    uu____40884
                                                                    ::
                                                                    uu____40904
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    "Retain comments in the logged SMT queries (requires --log_queries; default true)")
                                                                    ::
                                                                    uu____40870
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____40856
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try initially (default 2)")
                                                                    ::
                                                                    uu____40842
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "protect_top_level_axioms",
                                                                    BoolStr,
                                                                    "Guard nullary top-level symbols in the SMT encoding from provide ambient ground facts (default 'true')")
                                                                    ::
                                                                    uu____40828
                                                                     in
                                                                    uu____40794
                                                                    ::
                                                                    uu____40814
                                                                     in
                                                                  uu____40760
                                                                    ::
                                                                    uu____40780
                                                                   in
                                                                uu____40726
                                                                  ::
                                                                  uu____40746
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "include",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "path")),
                                                                "A directory in which to search for files included on the command line")
                                                                ::
                                                                uu____40712
                                                               in
                                                            uu____40678 ::
                                                              uu____40698
                                                             in
                                                          uu____40644 ::
                                                            uu____40664
                                                           in
                                                        uu____40610 ::
                                                          uu____40630
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "hint_file",
                                                        (PathStr "path"),
                                                        "Read/write hints to <path> (instead of module-specific hints files)")
                                                        :: uu____40596
                                                       in
                                                    uu____40562 ::
                                                      uu____40582
                                                     in
                                                  uu____40528 :: uu____40548
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "extract_namespace",
                                                  (Accumulated
                                                     (PostProcessed
                                                        (pp_lowercase,
                                                          (SimpleStr
                                                             "namespace name")))),
                                                  "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                  :: uu____40514
                                                 in
                                              (FStar_Getopt.noshort,
                                                "extract_module",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "module_name")))),
                                                "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                                :: uu____40500
                                               in
                                            (FStar_Getopt.noshort, "extract",
                                              (Accumulated
                                                 (SimpleStr
                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                              "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                              :: uu____40486
                                             in
                                          uu____40452 :: uu____40472  in
                                        uu____40418 :: uu____40438  in
                                      (FStar_Getopt.noshort, "dump_module",
                                        (Accumulated
                                           (SimpleStr "module_name")), "")
                                        :: uu____40404
                                       in
                                    uu____40370 :: uu____40390  in
                                  uu____40336 :: uu____40356  in
                                uu____40302 :: uu____40322  in
                              (FStar_Getopt.noshort, "dep",
                                (EnumStr ["make"; "graph"; "full"; "raw"]),
                                "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                                :: uu____40288
                               in
                            (FStar_Getopt.noshort, "defensive",
                              (EnumStr ["no"; "warn"; "fail"]),
                              "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                              :: uu____40274
                             in
                          (FStar_Getopt.noshort, "debug_level",
                            (Accumulated
                               (OpenEnumStr
                                  (["Low"; "Medium"; "High"; "Extreme"],
                                    "..."))),
                            "Control the verbosity of debugging info") ::
                            uu____40260
                           in
                        (FStar_Getopt.noshort, "debug",
                          (Accumulated (SimpleStr "module_name")),
                          "Print lots of debugging information while checking module")
                          :: uu____40246
                         in
                      (FStar_Getopt.noshort, "codegen-lib",
                        (Accumulated (SimpleStr "namespace")),
                        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                        :: uu____40232
                       in
                    (FStar_Getopt.noshort, "codegen",
                      (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                      "Generate code for further compilation to executable code, or build a compiler plugin")
                      :: uu____40218
                     in
                  uu____40184 :: uu____40204  in
                uu____40150 :: uu____40170  in
              (FStar_Getopt.noshort, "cache_dir",
                (PostProcessed (pp_validate_dir, (PathStr "dir"))),
                "Read and write .checked and .checked.lax in directory <dir>")
                :: uu____40136
               in
            uu____40102 :: uu____40122  in
          (FStar_Getopt.noshort, "already_cached",
            (Accumulated
               (SimpleStr
                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
            "\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")
            :: uu____40088
           in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____40074
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____40060
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___296_44325  ->
             match uu___296_44325 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____40046

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____44354  ->
    let uu____44357 = specs_with_types ()  in
    FStar_List.map
      (fun uu____44388  ->
         match uu____44388 with
         | (short,long,typ,doc) ->
             let uu____44410 =
               let uu____44424 = arg_spec_of_opt_type long typ  in
               (short, long, uu____44424, doc)  in
             mk_spec uu____44410) uu____44357

let (settable : Prims.string -> Prims.bool) =
  fun uu___297_44439  ->
    match uu___297_44439 with
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
    | uu____44562 -> false
  
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
       (fun uu____44661  ->
          match uu____44661 with
          | (uu____44676,x,uu____44678,uu____44679) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____44754  ->
          match uu____44754 with
          | (uu____44769,x,uu____44771,uu____44772) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____44788  ->
    let uu____44789 = specs ()  in display_usage_aux uu____44789
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____44821 -> true
    | uu____44824 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____44835 -> uu____44835
  
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
        (fun uu___759_44856  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____44873 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____44873
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____44909  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____44915 =
             let uu____44919 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____44919 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____44915)
       in
    let uu____44976 =
      let uu____44980 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____44980
       in
    (res, uu____44976)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____45022  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____45065 = specs ()  in
       FStar_Getopt.parse_cmdline uu____45065 (fun x  -> ())  in
     (let uu____45072 =
        let uu____45078 =
          let uu____45079 = FStar_List.map mk_string old_verify_module  in
          List uu____45079  in
        ("verify_module", uu____45078)  in
      set_option' uu____45072);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____45098 =
        let uu____45100 =
          let uu____45102 =
            let uu____45104 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____45104  in
          (FStar_String.length f1) - uu____45102  in
        uu____45100 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____45098  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____45117 = get_lax ()  in
    if uu____45117
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____45138 = module_name_of_file_name fn  in
    should_verify uu____45138
  
let (module_name_eq : Prims.string -> Prims.string -> Prims.bool) =
  fun m1  ->
    fun m2  -> (FStar_String.lowercase m1) = (FStar_String.lowercase m2)
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____45166 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____45166 (FStar_List.existsb (module_name_eq m))
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____45184 = should_verify m  in
    if uu____45184 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____45201  ->
    let cache_dir =
      let uu____45206 = get_cache_dir ()  in
      match uu____45206 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some c -> [c]  in
    let uu____45220 = get_no_default_includes ()  in
    if uu____45220
    then
      let uu____45226 = get_include ()  in
      FStar_List.append cache_dir uu____45226
    else
      (let lib_paths =
         let uu____45237 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____45237 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = FStar_String.op_Hat fstar_bin_directory "/.."
                in
             let defs = universe_include_path_base_dirs  in
             let uu____45253 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> FStar_String.op_Hat fstar_home x))
                in
             FStar_All.pipe_right uu____45253
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____45280 =
         let uu____45284 =
           let uu____45288 = get_include ()  in
           FStar_List.append uu____45288 ["."]  in
         FStar_List.append lib_paths uu____45284  in
       FStar_List.append cache_dir uu____45280)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____45315 = FStar_Util.smap_try_find file_map filename  in
    match uu____45315 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___810_45337  ->
               match () with
               | () ->
                   let uu____45341 = FStar_Util.is_path_absolute filename  in
                   if uu____45341
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____45357 =
                        let uu____45361 = include_path ()  in
                        FStar_List.rev uu____45361  in
                      FStar_Util.find_map uu____45357
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___809_45389 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____45409  ->
    let uu____45410 = get_prims ()  in
    match uu____45410 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____45419 = find_file filename  in
        (match uu____45419 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____45428 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____45428)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____45441  ->
    let uu____45442 = prims ()  in FStar_Util.basename uu____45442
  
let (pervasives : unit -> Prims.string) =
  fun uu____45450  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____45454 = find_file filename  in
    match uu____45454 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____45463 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____45463
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____45473  ->
    let uu____45474 = pervasives ()  in FStar_Util.basename uu____45474
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____45482  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____45486 = find_file filename  in
    match uu____45486 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____45495 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____45495
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____45508 = get_odir ()  in
    match uu____45508 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____45526 = get_cache_dir ()  in
    match uu____45526 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____45535 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____45535
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns  ->
    let cache = FStar_Util.smap_create (Prims.parse_int "31")  in
    let with_cache f s =
      let uu____45657 = FStar_Util.smap_try_find cache s  in
      match uu____45657 with
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
             let uu____45792 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____45792  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____45815 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              let s1 = FStar_Util.trim_string s  in
              if s1 = ""
              then []
              else
                with_cache
                  (fun s2  ->
                     let uu____45883 =
                       FStar_All.pipe_right (FStar_Util.splitlines s2)
                         (FStar_List.concatMap
                            (fun s3  -> FStar_Util.split s3 " "))
                        in
                     FStar_All.pipe_right uu____45883
                       (FStar_List.map parse_one_setting)) s1))
       in
    FStar_All.pipe_right uu____45815 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____45958 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____45958 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____45973  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____45982  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____45991  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____45998  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____46005  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____46012  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____46022 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____46033 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____46044 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____46055 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____46064  ->
    let uu____46065 = get_codegen ()  in
    FStar_Util.map_opt uu____46065
      (fun uu___298_46071  ->
         match uu___298_46071 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____46077 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____46090  ->
    let uu____46091 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____46091
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____46117  -> let uu____46118 = get_debug ()  in uu____46118 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____46135 = get_debug ()  in
    FStar_All.pipe_right uu____46135
      (FStar_List.existsb (module_name_eq modul))
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____46160 = get_debug ()  in
       FStar_All.pipe_right uu____46160
         (FStar_List.existsb (module_name_eq modul)))
        && (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____46175  ->
    let uu____46176 = get_defensive ()  in uu____46176 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____46186  ->
    let uu____46187 = get_defensive ()  in uu____46187 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46199  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____46206  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____46213  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____46220  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____46230 = get_dump_module ()  in
    FStar_All.pipe_right uu____46230 (FStar_List.existsb (module_name_eq s))
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____46245  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____46252  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____46262 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____46262
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____46298  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____46306  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____46313  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46322  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____46329  -> get_ide () 
let (print : unit -> Prims.bool) = fun uu____46336  -> get_print () 
let (print_in_place : unit -> Prims.bool) =
  fun uu____46343  -> get_print_in_place () 
let profile : 'a . (unit -> 'a) -> ('a -> Prims.string) -> 'a =
  fun f  ->
    fun msg  ->
      let uu____46374 = get_profile ()  in
      if uu____46374
      then
        let uu____46377 = FStar_Util.record_time f  in
        match uu____46377 with
        | (a,time) ->
            ((let uu____46388 = FStar_Util.string_of_int time  in
              let uu____46390 = msg a  in
              FStar_Util.print2 "Elapsed time %s ms: %s\n" uu____46388
                uu____46390);
             a)
      else f ()
  
let (protect_top_level_axioms : unit -> Prims.bool) =
  fun uu____46401  -> get_protect_top_level_axioms () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____46408  ->
    let uu____46409 = get_initial_fuel ()  in
    let uu____46411 = get_max_fuel ()  in Prims.min uu____46409 uu____46411
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____46419  ->
    let uu____46420 = get_initial_ifuel ()  in
    let uu____46422 = get_max_ifuel ()  in Prims.min uu____46420 uu____46422
  
let (interactive : unit -> Prims.bool) =
  fun uu____46430  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____46437  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____46446  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____46453  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____46460  -> get_log_queries () 
let (keep_query_captions : unit -> Prims.bool) =
  fun uu____46467  -> (log_queries ()) && (get_keep_query_captions ()) 
let (log_types : unit -> Prims.bool) = fun uu____46474  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____46481  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____46488  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____46495  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____46502  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____46508  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____46517  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____46524  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____46534 = get_no_extract ()  in
    FStar_All.pipe_right uu____46534 (FStar_List.existsb (module_name_eq s))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____46549  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____46556  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____46563  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____46570  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46579  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____46586  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____46593  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____46600  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____46607  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____46614  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____46621  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____46628  -> get_print_z3_statistics () 
let (query_stats : unit -> Prims.bool) =
  fun uu____46635  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____46642  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46651  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____46658  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____46665  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____46672  ->
    let uu____46673 = get_smtencoding_nl_arith_repr ()  in
    uu____46673 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____46683  ->
    let uu____46684 = get_smtencoding_nl_arith_repr ()  in
    uu____46684 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____46694  ->
    let uu____46695 = get_smtencoding_nl_arith_repr ()  in
    uu____46695 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____46705  ->
    let uu____46706 = get_smtencoding_l_arith_repr ()  in
    uu____46706 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____46716  ->
    let uu____46717 = get_smtencoding_l_arith_repr ()  in
    uu____46717 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____46727  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____46734  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____46741  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____46748  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____46755  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____46762  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____46769  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____46776  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____46783  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____46790  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____46797  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____46804  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____46811  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____46818  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____46827  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____46834  -> get_use_tactics () 
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu____46850  ->
    let uu____46851 = get_using_facts_from ()  in
    match uu____46851 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____46905  ->
    let uu____46906 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____46906
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____46917  ->
    let uu____46918 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____46918 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____46926 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____46937  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____46944  ->
    let uu____46945 = get_smt ()  in
    match uu____46945 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____46963  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____46970  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____46977  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____46984  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____46991  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____46998  ->
    (get_use_two_phase_tc ()) &&
      (let uu____47000 = lax ()  in Prims.op_Negation uu____47000)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____47008  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____47015  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____47022  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____47029  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____47036  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____47053 =
      let uu____47055 = trace_error ()  in Prims.op_Negation uu____47055  in
    if uu____47053
    then
      (push ();
       (let r =
          try
            (fun uu___1009_47070  ->
               match () with
               | () -> let uu____47075 = f ()  in FStar_Util.Inr uu____47075)
              ()
          with | uu___1008_47077 -> FStar_Util.Inl uu___1008_47077  in
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
        | (uu____47158,[]) -> true
        | (m2::ms,p::ps) ->
            (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
        | uu____47191 -> false  in
      let uu____47203 =
        FStar_All.pipe_right setting
          (FStar_Util.try_find
             (fun uu____47245  ->
                match uu____47245 with
                | (path,uu____47256) -> matches_path m_components path))
         in
      match uu____47203 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____47275,flag) -> flag
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____47304 = get_extract ()  in
    match uu____47304 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____47319 =
            let uu____47335 = get_no_extract ()  in
            let uu____47339 = get_extract_namespace ()  in
            let uu____47343 = get_extract_module ()  in
            (uu____47335, uu____47339, uu____47343)  in
          match uu____47319 with
          | ([],[],[]) -> ()
          | uu____47368 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         module_matches_namespace_filter m1 extract_setting)
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____47397 = get_extract_namespace ()  in
          match uu____47397 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____47425 = get_extract_module ()  in
          match uu____47425 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____47447 = no_extract m1  in Prims.op_Negation uu____47447)
          &&
          (let uu____47450 =
             let uu____47461 = get_extract_namespace ()  in
             let uu____47465 = get_extract_module ()  in
             (uu____47461, uu____47465)  in
           (match uu____47450 with
            | ([],[]) -> true
            | uu____47485 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  
let (should_be_already_cached : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____47505 = get_already_cached ()  in
    match uu____47505 with
    | FStar_Pervasives_Native.None  -> false
    | FStar_Pervasives_Native.Some already_cached_setting ->
        module_matches_namespace_filter m already_cached_setting
  
let (error_flags : unit -> error_flag Prims.list) =
  let cache = FStar_Util.smap_create (Prims.parse_int "10")  in
  fun uu____47538  ->
    let we = warn_error ()  in
    let uu____47541 = FStar_Util.smap_try_find cache we  in
    match uu____47541 with
    | FStar_Pervasives_Native.None  ->
        let r = parse_warn_error we  in (FStar_Util.smap_add cache we r; r)
    | FStar_Pervasives_Native.Some r -> r
  