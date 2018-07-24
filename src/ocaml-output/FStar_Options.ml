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
  fun projectee  -> match projectee with | Low  -> true | uu____59 -> false 
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____65 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | High  -> true | uu____71 -> false 
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____77 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____84 -> false
  
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
    match projectee with | Bool _0 -> true | uu____125 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____139 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____153 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____167 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____183 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____202 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _0_4  -> Bool _0_4 
let (mk_string : Prims.string -> option_val) = fun _0_5  -> String _0_5 
let (mk_path : Prims.string -> option_val) = fun _0_6  -> Path _0_6 
let (mk_int : Prims.int -> option_val) = fun _0_7  -> Int _0_7 
let (mk_list : option_val Prims.list -> option_val) = fun _0_8  -> List _0_8 
type options =
  | Set 
  | Reset 
  | Restore 
let (uu___is_Set : options -> Prims.bool) =
  fun projectee  -> match projectee with | Set  -> true | uu____230 -> false 
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reset  -> true | uu____236 -> false
  
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee  ->
    match projectee with | Restore  -> true | uu____242 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____260  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____284  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____308  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___76_332  ->
    match uu___76_332 with
    | Bool b -> b
    | uu____334 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___77_339  ->
    match uu___77_339 with
    | Int b -> b
    | uu____341 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___78_346  ->
    match uu___78_346 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____349 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___79_356  ->
    match uu___79_356 with
    | List ts -> ts
    | uu____362 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____371 .
    (option_val -> 'Auu____371) -> option_val -> 'Auu____371 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____389 = as_list' x  in
      FStar_All.pipe_right uu____389 (FStar_List.map as_t)
  
let as_option :
  'Auu____402 .
    (option_val -> 'Auu____402) ->
      option_val -> 'Auu____402 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___80_417  ->
      match uu___80_417 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____421 = as_t v1  in FStar_Pervasives_Native.Some uu____421
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___81_428  ->
    match uu___81_428 with
    | List ls ->
        let uu____434 =
          FStar_List.map
            (fun l  ->
               let uu____444 = as_string l  in FStar_Util.split uu____444 ",")
            ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____434
    | uu____451 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (peek : unit -> optionstate) =
  fun uu____483  ->
    let uu____484 =
      let uu____487 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____487  in
    FStar_List.hd uu____484
  
let (pop : unit -> unit) =
  fun uu____525  ->
    let uu____526 = FStar_ST.op_Bang fstar_options  in
    match uu____526 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____560::[] -> failwith "TOO MANY POPS!"
    | uu____567::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____608  ->
    let uu____609 =
      let uu____614 =
        let uu____617 =
          let uu____620 = FStar_ST.op_Bang fstar_options  in
          FStar_List.hd uu____620  in
        FStar_List.map FStar_Util.smap_copy uu____617  in
      let uu____654 = FStar_ST.op_Bang fstar_options  in uu____614 ::
        uu____654
       in
    FStar_ST.op_Colon_Equals fstar_options uu____609
  
let (internal_pop : unit -> unit) =
  fun uu____719  ->
    let curstack =
      let uu____723 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____723  in
    let stack' = FStar_List.tl curstack  in
    let uu____760 =
      let uu____765 =
        let uu____770 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____770  in
      stack' :: uu____765  in
    FStar_ST.op_Colon_Equals fstar_options uu____760
  
let (internal_push : unit -> unit) =
  fun uu____837  ->
    let curstack =
      let uu____841 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____841  in
    let stack' =
      let uu____878 =
        let uu____879 = FStar_List.hd curstack  in
        FStar_Util.smap_copy uu____879  in
      uu____878 :: curstack  in
    let uu____882 =
      let uu____887 =
        let uu____892 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____892  in
      stack' :: uu____887  in
    FStar_ST.op_Colon_Equals fstar_options uu____882
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____960 = FStar_ST.op_Bang fstar_options  in
    match uu____960 with
    | [] -> failwith "set on empty option stack"
    | (uu____994::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
  
let (snapshot : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____1042  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____1066 = peek ()  in FStar_Util.smap_add uu____1066 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____1077  -> match uu____1077 with | (k,v1) -> set_option k v1 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____1106 =
      let uu____1109 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____1109
       in
    FStar_ST.op_Colon_Equals light_off_files uu____1106
  
let (defaults :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 Prims.list) =
  [("__temp_no_proj", (List []));
  ("__temp_fast_implicits", (Bool false));
  ("abort_on", (Int (Prims.parse_int "0")));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
  ("cache_checked_modules", (Bool false));
  ("cache_dir", Unset);
  ("cache_off", (Bool false));
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
  ("indent", (Bool false));
  ("initial_fuel", (Int (Prims.parse_int "2")));
  ("initial_ifuel", (Int (Prims.parse_int "1")));
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
  ("use_extracted_interfaces", (Bool false))] 
let (init : unit -> unit) =
  fun uu____1576  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1593  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1658 =
      let uu____1661 = peek ()  in FStar_Util.smap_try_find uu____1661 s  in
    match uu____1658 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1671 . Prims.string -> (option_val -> 'Auu____1671) -> 'Auu____1671
  = fun s  -> fun c  -> let uu____1687 = get_option s  in c uu____1687 
let (get_abort_on : unit -> Prims.int) =
  fun uu____1692  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1697  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1704  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1711  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1718  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1725  -> lookup_opt "cache_off" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1732  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1741  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1750  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1759  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____1766  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1773  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1780  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1785  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1790  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1797  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1804  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1809  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1818  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1831  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1840  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1847  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1852  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1857  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1864  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1871  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1876  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1883  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1890  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1895  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1900  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1905  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1912  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1919  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1924  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1929  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1934  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1939  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1944  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1949  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1954  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1961  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1968  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____1973  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1978  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1983  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1990  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____1997  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2004  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____2011  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____2016  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____2021  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____2026  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____2031  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____2036  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____2041  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____2046  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____2051  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2058  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____2065  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2072  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____2079  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____2084  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____2089  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____2094  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____2099  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____2104  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____2109  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____2114  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____2119  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____2124  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____2129  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____2134  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____2139  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____2144  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____2149  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____2154  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____2159  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2166  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____2173  ->
    let uu____2174 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____2174
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2183  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2196  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____2205  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____2214  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____2221  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____2226  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____2233  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____2240  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____2245  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____2250  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____2255  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____2260  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____2265  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____2270  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____2275  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____2280  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___82_2285  ->
    match uu___82_2285 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____2297 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____2303 = get_debug_level ()  in
    FStar_All.pipe_right uu____2303
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2436  ->
    let uu____2437 =
      let uu____2438 = FStar_ST.op_Bang _version  in
      let uu____2458 = FStar_ST.op_Bang _platform  in
      let uu____2478 = FStar_ST.op_Bang _compiler  in
      let uu____2498 = FStar_ST.op_Bang _date  in
      let uu____2518 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2438
        uu____2458 uu____2478 uu____2498 uu____2518
       in
    FStar_Util.print_string uu____2437
  
let display_usage_aux :
  'Auu____2544 'Auu____2545 .
    ('Auu____2544,Prims.string,'Auu____2545 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2593  ->
         match uu____2593 with
         | (uu____2604,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2616 =
                      let uu____2617 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2617  in
                    FStar_Util.print_string uu____2616
                  else
                    (let uu____2619 =
                       let uu____2620 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2620 doc  in
                     FStar_Util.print_string uu____2619)
              | FStar_Getopt.OneArg (uu____2621,argname) ->
                  if doc = ""
                  then
                    let uu____2629 =
                      let uu____2630 = FStar_Util.colorize_bold flag  in
                      let uu____2631 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2630 uu____2631
                       in
                    FStar_Util.print_string uu____2629
                  else
                    (let uu____2633 =
                       let uu____2634 = FStar_Util.colorize_bold flag  in
                       let uu____2635 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2634
                         uu____2635 doc
                        in
                     FStar_Util.print_string uu____2633))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2663 = o  in
    match uu____2663 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2699 =
                let uu____2700 = f ()  in set_option name uu____2700  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2715 = f x  in set_option name uu____2715
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2735 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2735  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2758 =
        let uu____2761 = lookup_opt name as_list'  in
        FStar_List.append uu____2761 [value]  in
      mk_list uu____2758
  
let accumulate_string :
  'Auu____2774 .
    Prims.string -> ('Auu____2774 -> Prims.string) -> 'Auu____2774 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2795 =
          let uu____2796 =
            let uu____2797 = post_processor value  in mk_string uu____2797
             in
          accumulated_option name uu____2796  in
        set_option name uu____2795
  
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
  | OpenEnumStr of (Prims.string Prims.list,Prims.string)
  FStar_Pervasives_Native.tuple2 
  | PostProcessed of (option_val -> option_val,opt_type)
  FStar_Pervasives_Native.tuple2 
  | Accumulated of opt_type 
  | ReverseAccumulated of opt_type 
  | WithSideEffect of (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2 
let (uu___is_Const : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____2893 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2907 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2920 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2927 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2941 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2957 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____2983 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____3022 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____3057 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____3071 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____3092 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____3130 -> true
    | uu____3131 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____3138 -> uu____3138
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___87_3156  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____3158 ->
                      let uu____3159 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____3159 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____3163 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____3163
                  | PathStr uu____3166 -> mk_path str_val
                  | SimpleStr uu____3167 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____3172 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____3187 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____3187
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
            let uu____3206 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____3206
  
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ  ->
    let desc_of_enum cases =
      FStar_Pervasives_Native.Some
        (Prims.strcat "[" (Prims.strcat (FStar_String.concat "|" cases) "]"))
       in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____3243,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____3253,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____3280 = desc_of_opt_type typ  in
      match uu____3280 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____3286  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____3303 =
      let uu____3304 = as_string s  in FStar_String.lowercase uu____3304  in
    mk_string uu____3303
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____3352  ->
    let uu____3364 =
      let uu____3376 =
        let uu____3388 =
          let uu____3400 =
            let uu____3410 =
              let uu____3411 = mk_bool true  in Const uu____3411  in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____3410,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
             in
          let uu____3413 =
            let uu____3425 =
              let uu____3437 =
                let uu____3447 =
                  let uu____3448 = mk_bool true  in Const uu____3448  in
                (FStar_Getopt.noshort, "cache_off", uu____3447,
                  "Do not read or write any .checked files")
                 in
              let uu____3450 =
                let uu____3462 =
                  let uu____3474 =
                    let uu____3486 =
                      let uu____3498 =
                        let uu____3510 =
                          let uu____3522 =
                            let uu____3534 =
                              let uu____3544 =
                                let uu____3545 = mk_bool true  in
                                Const uu____3545  in
                              (FStar_Getopt.noshort, "detail_errors",
                                uu____3544,
                                "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                               in
                            let uu____3547 =
                              let uu____3559 =
                                let uu____3569 =
                                  let uu____3570 = mk_bool true  in
                                  Const uu____3570  in
                                (FStar_Getopt.noshort, "detail_hint_replay",
                                  uu____3569,
                                  "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                 in
                              let uu____3572 =
                                let uu____3584 =
                                  let uu____3594 =
                                    let uu____3595 = mk_bool true  in
                                    Const uu____3595  in
                                  (FStar_Getopt.noshort, "doc", uu____3594,
                                    "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                   in
                                let uu____3597 =
                                  let uu____3609 =
                                    let uu____3621 =
                                      let uu____3631 =
                                        let uu____3632 = mk_bool true  in
                                        Const uu____3632  in
                                      (FStar_Getopt.noshort,
                                        "eager_inference", uu____3631,
                                        "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                       in
                                    let uu____3634 =
                                      let uu____3646 =
                                        let uu____3656 =
                                          let uu____3657 = mk_bool true  in
                                          Const uu____3657  in
                                        (FStar_Getopt.noshort,
                                          "eager_subtyping", uu____3656,
                                          "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                         in
                                      let uu____3659 =
                                        let uu____3671 =
                                          let uu____3683 =
                                            let uu____3695 =
                                              let uu____3707 =
                                                let uu____3717 =
                                                  let uu____3718 =
                                                    mk_bool true  in
                                                  Const uu____3718  in
                                                (FStar_Getopt.noshort,
                                                  "expose_interfaces",
                                                  uu____3717,
                                                  "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                 in
                                              let uu____3720 =
                                                let uu____3732 =
                                                  let uu____3742 =
                                                    let uu____3743 =
                                                      mk_bool true  in
                                                    Const uu____3743  in
                                                  (FStar_Getopt.noshort,
                                                    "hide_uvar_nums",
                                                    uu____3742,
                                                    "Don't print unification variable numbers")
                                                   in
                                                let uu____3745 =
                                                  let uu____3757 =
                                                    let uu____3769 =
                                                      let uu____3779 =
                                                        let uu____3780 =
                                                          mk_bool true  in
                                                        Const uu____3780  in
                                                      (FStar_Getopt.noshort,
                                                        "hint_info",
                                                        uu____3779,
                                                        "Print information regarding hints (deprecated; use --query_stats instead)")
                                                       in
                                                    let uu____3782 =
                                                      let uu____3794 =
                                                        let uu____3804 =
                                                          let uu____3805 =
                                                            mk_bool true  in
                                                          Const uu____3805
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "in", uu____3804,
                                                          "Legacy interactive mode; reads input from stdin")
                                                         in
                                                      let uu____3807 =
                                                        let uu____3819 =
                                                          let uu____3829 =
                                                            let uu____3830 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3830
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "ide",
                                                            uu____3829,
                                                            "JSON-based interactive mode for IDEs")
                                                           in
                                                        let uu____3832 =
                                                          let uu____3844 =
                                                            let uu____3856 =
                                                              let uu____3866
                                                                =
                                                                let uu____3867
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____3867
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "indent",
                                                                uu____3866,
                                                                "Parses and outputs the files on the command line")
                                                               in
                                                            let uu____3869 =
                                                              let uu____3881
                                                                =
                                                                let uu____3893
                                                                  =
                                                                  let uu____3905
                                                                    =
                                                                    let uu____3915
                                                                    =
                                                                    let uu____3916
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3916
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3915,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                  let uu____3918
                                                                    =
                                                                    let uu____3930
                                                                    =
                                                                    let uu____3942
                                                                    =
                                                                    let uu____3952
                                                                    =
                                                                    let uu____3953
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3953
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3952,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3955
                                                                    =
                                                                    let uu____3967
                                                                    =
                                                                    let uu____3977
                                                                    =
                                                                    let uu____3978
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3978
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3977,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____3980
                                                                    =
                                                                    let uu____3992
                                                                    =
                                                                    let uu____4004
                                                                    =
                                                                    let uu____4016
                                                                    =
                                                                    let uu____4028
                                                                    =
                                                                    let uu____4038
                                                                    =
                                                                    let uu____4039
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4039
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____4038,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____4041
                                                                    =
                                                                    let uu____4053
                                                                    =
                                                                    let uu____4065
                                                                    =
                                                                    let uu____4075
                                                                    =
                                                                    let uu____4076
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4076
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____4075,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____4078
                                                                    =
                                                                    let uu____4090
                                                                    =
                                                                    let uu____4102
                                                                    =
                                                                    let uu____4112
                                                                    =
                                                                    let uu____4113
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4113
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____4112,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____4115
                                                                    =
                                                                    let uu____4127
                                                                    =
                                                                    let uu____4137
                                                                    =
                                                                    let uu____4138
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4138
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____4137,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____4140
                                                                    =
                                                                    let uu____4152
                                                                    =
                                                                    let uu____4162
                                                                    =
                                                                    let uu____4163
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4163
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____4162,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____4165
                                                                    =
                                                                    let uu____4177
                                                                    =
                                                                    let uu____4189
                                                                    =
                                                                    let uu____4201
                                                                    =
                                                                    let uu____4211
                                                                    =
                                                                    let uu____4212
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4212
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____4211,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____4214
                                                                    =
                                                                    let uu____4226
                                                                    =
                                                                    let uu____4236
                                                                    =
                                                                    let uu____4237
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4237
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____4236,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____4239
                                                                    =
                                                                    let uu____4251
                                                                    =
                                                                    let uu____4261
                                                                    =
                                                                    let uu____4262
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4262
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____4261,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____4264
                                                                    =
                                                                    let uu____4276
                                                                    =
                                                                    let uu____4286
                                                                    =
                                                                    let uu____4287
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4287
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____4286,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____4289
                                                                    =
                                                                    let uu____4301
                                                                    =
                                                                    let uu____4311
                                                                    =
                                                                    let uu____4312
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4312
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____4311,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____4314
                                                                    =
                                                                    let uu____4326
                                                                    =
                                                                    let uu____4336
                                                                    =
                                                                    let uu____4337
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4337
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____4336,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____4339
                                                                    =
                                                                    let uu____4351
                                                                    =
                                                                    let uu____4361
                                                                    =
                                                                    let uu____4362
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4362
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____4361,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____4364
                                                                    =
                                                                    let uu____4376
                                                                    =
                                                                    let uu____4386
                                                                    =
                                                                    let uu____4387
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4387
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____4386,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____4389
                                                                    =
                                                                    let uu____4401
                                                                    =
                                                                    let uu____4411
                                                                    =
                                                                    let uu____4412
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4412
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____4411,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____4414
                                                                    =
                                                                    let uu____4426
                                                                    =
                                                                    let uu____4438
                                                                    =
                                                                    let uu____4448
                                                                    =
                                                                    let uu____4449
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4449
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4448,
                                                                    " ")  in
                                                                    let uu____4451
                                                                    =
                                                                    let uu____4463
                                                                    =
                                                                    let uu____4475
                                                                    =
                                                                    let uu____4487
                                                                    =
                                                                    let uu____4499
                                                                    =
                                                                    let uu____4511
                                                                    =
                                                                    let uu____4521
                                                                    =
                                                                    let uu____4522
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4522
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4521,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4524
                                                                    =
                                                                    let uu____4536
                                                                    =
                                                                    let uu____4546
                                                                    =
                                                                    let uu____4547
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4547
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____4546,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____4549
                                                                    =
                                                                    let uu____4561
                                                                    =
                                                                    let uu____4571
                                                                    =
                                                                    let uu____4572
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4572
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____4571,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____4574
                                                                    =
                                                                    let uu____4586
                                                                    =
                                                                    let uu____4596
                                                                    =
                                                                    let uu____4597
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4597
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4596,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4599
                                                                    =
                                                                    let uu____4611
                                                                    =
                                                                    let uu____4623
                                                                    =
                                                                    let uu____4633
                                                                    =
                                                                    let uu____4634
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4634
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____4633,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____4636
                                                                    =
                                                                    let uu____4648
                                                                    =
                                                                    let uu____4660
                                                                    =
                                                                    let uu____4670
                                                                    =
                                                                    let uu____4671
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4671
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4670,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4673
                                                                    =
                                                                    let uu____4685
                                                                    =
                                                                    let uu____4695
                                                                    =
                                                                    let uu____4696
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4696
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4695,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4698
                                                                    =
                                                                    let uu____4710
                                                                    =
                                                                    let uu____4720
                                                                    =
                                                                    let uu____4721
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4721
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4720,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4723
                                                                    =
                                                                    let uu____4735
                                                                    =
                                                                    let uu____4745
                                                                    =
                                                                    let uu____4746
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4746
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4745,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4748
                                                                    =
                                                                    let uu____4760
                                                                    =
                                                                    let uu____4770
                                                                    =
                                                                    let uu____4771
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4771
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4770,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4773
                                                                    =
                                                                    let uu____4785
                                                                    =
                                                                    let uu____4795
                                                                    =
                                                                    let uu____4796
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4796
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4795,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4798
                                                                    =
                                                                    let uu____4810
                                                                    =
                                                                    let uu____4820
                                                                    =
                                                                    let uu____4821
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4821
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4820,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4823
                                                                    =
                                                                    let uu____4835
                                                                    =
                                                                    let uu____4845
                                                                    =
                                                                    let uu____4846
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4846
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4845,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4848
                                                                    =
                                                                    let uu____4860
                                                                    =
                                                                    let uu____4872
                                                                    =
                                                                    let uu____4882
                                                                    =
                                                                    let uu____4883
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4883
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____4882,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____4885
                                                                    =
                                                                    let uu____4897
                                                                    =
                                                                    let uu____4907
                                                                    =
                                                                    let uu____4908
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4908
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4907,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4910
                                                                    =
                                                                    let uu____4922
                                                                    =
                                                                    let uu____4934
                                                                    =
                                                                    let uu____4946
                                                                    =
                                                                    let uu____4958
                                                                    =
                                                                    let uu____4968
                                                                    =
                                                                    let uu____4969
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4969
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4968,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____4971
                                                                    =
                                                                    let uu____4983
                                                                    =
                                                                    let uu____4993
                                                                    =
                                                                    let uu____4994
                                                                    =
                                                                    let uu____5002
                                                                    =
                                                                    let uu____5003
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5003
                                                                     in
                                                                    ((fun
                                                                    uu____5009
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____5002)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____4994
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____4993,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____5013
                                                                    =
                                                                    let uu____5025
                                                                    =
                                                                    let uu____5035
                                                                    =
                                                                    let uu____5036
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5036
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____5035,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____5038
                                                                    =
                                                                    let uu____5050
                                                                    =
                                                                    let uu____5062
                                                                    =
                                                                    let uu____5072
                                                                    =
                                                                    let uu____5073
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5073
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____5072,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____5075
                                                                    =
                                                                    let uu____5087
                                                                    =
                                                                    let uu____5099
                                                                    =
                                                                    let uu____5111
                                                                    =
                                                                    let uu____5123
                                                                    =
                                                                    let uu____5135
                                                                    =
                                                                    let uu____5145
                                                                    =
                                                                    let uu____5146
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5146
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____5145,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____5148
                                                                    =
                                                                    let uu____5160
                                                                    =
                                                                    let uu____5170
                                                                    =
                                                                    let uu____5171
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5171
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____5170,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____5173
                                                                    =
                                                                    let uu____5185
                                                                    =
                                                                    let uu____5197
                                                                    =
                                                                    let uu____5209
                                                                    =
                                                                    let uu____5219
                                                                    =
                                                                    let uu____5220
                                                                    =
                                                                    let uu____5228
                                                                    =
                                                                    let uu____5229
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5229
                                                                     in
                                                                    ((fun
                                                                    uu____5234
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____5228)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____5220
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____5219,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____5255
                                                                    =
                                                                    let uu____5267
                                                                    =
                                                                    let uu____5277
                                                                    =
                                                                    let uu____5278
                                                                    =
                                                                    let uu____5286
                                                                    =
                                                                    let uu____5287
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5287
                                                                     in
                                                                    ((fun
                                                                    uu____5292
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____5286)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____5278
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____5277,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____5313
                                                                    =
                                                                    let uu____5325
                                                                    =
                                                                    let uu____5335
                                                                    =
                                                                    let uu____5336
                                                                    =
                                                                    let uu____5344
                                                                    =
                                                                    let uu____5345
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5345
                                                                     in
                                                                    ((fun
                                                                    uu____5351
                                                                     ->
                                                                    (
                                                                    let uu____5353
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____5353);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____5344)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____5336
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____5335,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____5325]
                                                                     in
                                                                    uu____5267
                                                                    ::
                                                                    uu____5313
                                                                     in
                                                                    uu____5209
                                                                    ::
                                                                    uu____5255
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____5197
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____5185
                                                                     in
                                                                    uu____5160
                                                                    ::
                                                                    uu____5173
                                                                     in
                                                                    uu____5135
                                                                    ::
                                                                    uu____5148
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____5123
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____5111
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____5099
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____5087
                                                                     in
                                                                    uu____5062
                                                                    ::
                                                                    uu____5075
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____5050
                                                                     in
                                                                    uu____5025
                                                                    ::
                                                                    uu____5038
                                                                     in
                                                                    uu____4983
                                                                    ::
                                                                    uu____5013
                                                                     in
                                                                    uu____4958
                                                                    ::
                                                                    uu____4971
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4946
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4934
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4922
                                                                     in
                                                                    uu____4897
                                                                    ::
                                                                    uu____4910
                                                                     in
                                                                    uu____4872
                                                                    ::
                                                                    uu____4885
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4860
                                                                     in
                                                                    uu____4835
                                                                    ::
                                                                    uu____4848
                                                                     in
                                                                    uu____4810
                                                                    ::
                                                                    uu____4823
                                                                     in
                                                                    uu____4785
                                                                    ::
                                                                    uu____4798
                                                                     in
                                                                    uu____4760
                                                                    ::
                                                                    uu____4773
                                                                     in
                                                                    uu____4735
                                                                    ::
                                                                    uu____4748
                                                                     in
                                                                    uu____4710
                                                                    ::
                                                                    uu____4723
                                                                     in
                                                                    uu____4685
                                                                    ::
                                                                    uu____4698
                                                                     in
                                                                    uu____4660
                                                                    ::
                                                                    uu____4673
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____4648
                                                                     in
                                                                    uu____4623
                                                                    ::
                                                                    uu____4636
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4611
                                                                     in
                                                                    uu____4586
                                                                    ::
                                                                    uu____4599
                                                                     in
                                                                    uu____4561
                                                                    ::
                                                                    uu____4574
                                                                     in
                                                                    uu____4536
                                                                    ::
                                                                    uu____4549
                                                                     in
                                                                    uu____4511
                                                                    ::
                                                                    uu____4524
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4499
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4487
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4475
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4463
                                                                     in
                                                                    uu____4438
                                                                    ::
                                                                    uu____4451
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____4426
                                                                     in
                                                                    uu____4401
                                                                    ::
                                                                    uu____4414
                                                                     in
                                                                    uu____4376
                                                                    ::
                                                                    uu____4389
                                                                     in
                                                                    uu____4351
                                                                    ::
                                                                    uu____4364
                                                                     in
                                                                    uu____4326
                                                                    ::
                                                                    uu____4339
                                                                     in
                                                                    uu____4301
                                                                    ::
                                                                    uu____4314
                                                                     in
                                                                    uu____4276
                                                                    ::
                                                                    uu____4289
                                                                     in
                                                                    uu____4251
                                                                    ::
                                                                    uu____4264
                                                                     in
                                                                    uu____4226
                                                                    ::
                                                                    uu____4239
                                                                     in
                                                                    uu____4201
                                                                    ::
                                                                    uu____4214
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____4189
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____4177
                                                                     in
                                                                    uu____4152
                                                                    ::
                                                                    uu____4165
                                                                     in
                                                                    uu____4127
                                                                    ::
                                                                    uu____4140
                                                                     in
                                                                    uu____4102
                                                                    ::
                                                                    uu____4115
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____4090
                                                                     in
                                                                    uu____4065
                                                                    ::
                                                                    uu____4078
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____4053
                                                                     in
                                                                    uu____4028
                                                                    ::
                                                                    uu____4041
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____4016
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____4004
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____3992
                                                                     in
                                                                    uu____3967
                                                                    ::
                                                                    uu____3980
                                                                     in
                                                                    uu____3942
                                                                    ::
                                                                    uu____3955
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3930
                                                                     in
                                                                  uu____3905
                                                                    ::
                                                                    uu____3918
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_ifuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                  ::
                                                                  uu____3893
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_fuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of recursive functions to try initially (default 2)")
                                                                :: uu____3881
                                                               in
                                                            uu____3856 ::
                                                              uu____3869
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "include",
                                                            (ReverseAccumulated
                                                               (PathStr
                                                                  "path")),
                                                            "A directory in which to search for files included on the command line")
                                                            :: uu____3844
                                                           in
                                                        uu____3819 ::
                                                          uu____3832
                                                         in
                                                      uu____3794 ::
                                                        uu____3807
                                                       in
                                                    uu____3769 :: uu____3782
                                                     in
                                                  (FStar_Getopt.noshort,
                                                    "hint_file",
                                                    (PathStr "path"),
                                                    "Read/write hints to <path> (instead of module-specific hints files)")
                                                    :: uu____3757
                                                   in
                                                uu____3732 :: uu____3745  in
                                              uu____3707 :: uu____3720  in
                                            (FStar_Getopt.noshort,
                                              "extract_namespace",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "namespace name")))),
                                              "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                              :: uu____3695
                                             in
                                          (FStar_Getopt.noshort,
                                            "extract_module",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr "module_name")))),
                                            "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                            :: uu____3683
                                           in
                                        (FStar_Getopt.noshort, "extract",
                                          (Accumulated
                                             (SimpleStr
                                                "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                          "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                          :: uu____3671
                                         in
                                      uu____3646 :: uu____3659  in
                                    uu____3621 :: uu____3634  in
                                  (FStar_Getopt.noshort, "dump_module",
                                    (Accumulated (SimpleStr "module_name")),
                                    "") :: uu____3609
                                   in
                                uu____3584 :: uu____3597  in
                              uu____3559 :: uu____3572  in
                            uu____3534 :: uu____3547  in
                          (FStar_Getopt.noshort, "dep",
                            (EnumStr ["make"; "graph"; "full"]),
                            "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                            :: uu____3522
                           in
                        (FStar_Getopt.noshort, "defensive",
                          (EnumStr ["no"; "warn"; "fail"]),
                          "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                          :: uu____3510
                         in
                      (FStar_Getopt.noshort, "debug_level",
                        (Accumulated
                           (OpenEnumStr
                              (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                        "Control the verbosity of debugging info") ::
                        uu____3498
                       in
                    (FStar_Getopt.noshort, "debug",
                      (Accumulated (SimpleStr "module_name")),
                      "Print lots of debugging information while checking module")
                      :: uu____3486
                     in
                  (FStar_Getopt.noshort, "codegen-lib",
                    (Accumulated (SimpleStr "namespace")),
                    "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                    :: uu____3474
                   in
                (FStar_Getopt.noshort, "codegen",
                  (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                  "Generate code for further compilation to executable code, or build a compiler plugin")
                  :: uu____3462
                 in
              uu____3437 :: uu____3450  in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____3425
             in
          uu____3400 :: uu____3413  in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____3388
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____3376
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___83_6334  ->
             match uu___83_6334 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____3364

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____6357  ->
    let uu____6360 = specs_with_types ()  in
    FStar_List.map
      (fun uu____6387  ->
         match uu____6387 with
         | (short,long,typ,doc) ->
             let uu____6403 =
               let uu____6415 = arg_spec_of_opt_type long typ  in
               (short, long, uu____6415, doc)  in
             mk_spec uu____6403) uu____6360

let (settable : Prims.string -> Prims.bool) =
  fun uu___84_6425  ->
    match uu___84_6425 with
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
    | uu____6426 -> false
  
let (resettable : Prims.string -> Prims.bool) =
  fun s  ->
    (((settable s) || (s = "z3seed")) || (s = "z3cliopt")) ||
      (s = "using_facts_from")
  
let (all_specs : FStar_Getopt.opt Prims.list) = specs () 
let (all_specs_with_types :
  (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  = specs_with_types () 
let (settable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____6500  ->
          match uu____6500 with
          | (uu____6512,x,uu____6514,uu____6515) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____6577  ->
          match uu____6577 with
          | (uu____6589,x,uu____6591,uu____6592) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____6603  ->
    let uu____6604 = specs ()  in display_usage_aux uu____6604
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____6628 -> true
    | uu____6629 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____6636 -> uu____6636
  
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
        (fun uu___89_6653  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____6664 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____6664
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____6692  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____6697 =
             let uu____6700 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____6700 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____6697)
       in
    let uu____6749 =
      let uu____6752 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6752
       in
    (res, uu____6749)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6786  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6821 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6821 (fun x  -> ())  in
     (let uu____6827 =
        let uu____6832 =
          let uu____6833 = FStar_List.map mk_string old_verify_module  in
          List uu____6833  in
        ("verify_module", uu____6832)  in
      set_option' uu____6827);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6843 =
        let uu____6844 =
          let uu____6845 =
            let uu____6846 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6846  in
          (FStar_String.length f1) - uu____6845  in
        uu____6844 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6843  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6852 = get_lax ()  in
    if uu____6852
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6862 = module_name_of_file_name fn  in should_verify uu____6862
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6868 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6868
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6876 = should_verify m  in
    if uu____6876 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6884  ->
    let uu____6885 = get_no_default_includes ()  in
    if uu____6885
    then get_include ()
    else
      (let lib_paths =
         let uu____6892 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6892 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6901 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6901
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6915 =
         let uu____6918 = get_include ()  in
         FStar_List.append uu____6918 ["."]  in
       FStar_List.append lib_paths uu____6915)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____6931 = FStar_Util.smap_try_find file_map filename  in
    match uu____6931 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___91_6944  ->
               match () with
               | () ->
                   let uu____6947 = FStar_Util.is_path_absolute filename  in
                   if uu____6947
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____6954 =
                        let uu____6957 = include_path ()  in
                        FStar_List.rev uu____6957  in
                      FStar_Util.find_map uu____6954
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___90_6969 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____6980  ->
    let uu____6981 = get_prims ()  in
    match uu____6981 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____6985 = find_file filename  in
        (match uu____6985 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____6989 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____6989)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____6995  ->
    let uu____6996 = prims ()  in FStar_Util.basename uu____6996
  
let (pervasives : unit -> Prims.string) =
  fun uu____7001  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____7003 = find_file filename  in
    match uu____7003 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____7007 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____7007
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____7012  ->
    let uu____7013 = pervasives ()  in FStar_Util.basename uu____7013
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____7018  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____7020 = find_file filename  in
    match uu____7020 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____7024 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____7024
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____7030 = get_odir ()  in
    match uu____7030 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____7039 = get_cache_dir ()  in
    match uu____7039 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____7043 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____7043
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun ns  ->
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if FStar_Util.starts_with s "-"
        then
          (let path =
             let uu____7109 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____7109  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____7117 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____7117 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____7187 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____7187 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____7196  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____7201  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7208  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____7213  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____7218  -> get_cache_off () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____7224 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____7230 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____7236 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____7242 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____7249  ->
    let uu____7250 = get_codegen ()  in
    FStar_Util.map_opt uu____7250
      (fun uu___85_7254  ->
         match uu___85_7254 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____7255 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____7264  ->
    let uu____7265 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____7265
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____7282  -> let uu____7283 = get_debug ()  in uu____7283 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____7293 = get_debug ()  in
    FStar_All.pipe_right uu____7293 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____7310 = get_debug ()  in
       FStar_All.pipe_right uu____7310 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____7319  -> let uu____7320 = get_defensive ()  in uu____7320 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____7325  ->
    let uu____7326 = get_defensive ()  in uu____7326 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7333  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____7338  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____7343  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____7348  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____7354 = get_dump_module ()  in
    FStar_All.pipe_right uu____7354 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____7363  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____7368  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____7374 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____7374
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____7404  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____7409  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____7414  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7421  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____7426  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____7431  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____7436  ->
    let uu____7437 = get_initial_fuel ()  in
    let uu____7438 = get_max_fuel ()  in Prims.min uu____7437 uu____7438
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____7443  ->
    let uu____7444 = get_initial_ifuel ()  in
    let uu____7445 = get_max_ifuel ()  in Prims.min uu____7444 uu____7445
  
let (interactive : unit -> Prims.bool) =
  fun uu____7450  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____7455  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____7462  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____7467  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____7472  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____7477  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____7482  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____7487  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____7492  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____7497  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____7502  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____7507  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____7512  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____7519 = get_no_extract ()  in
    FStar_All.pipe_right uu____7519
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____7530  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____7535  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____7540  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____7545  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7552  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____7557  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____7562  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____7567  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____7572  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____7577  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____7582  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____7587  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____7592  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____7597  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7604  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____7609  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____7614  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____7619  ->
    let uu____7620 = get_smtencoding_nl_arith_repr ()  in
    uu____7620 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____7625  ->
    let uu____7626 = get_smtencoding_nl_arith_repr ()  in
    uu____7626 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____7631  ->
    let uu____7632 = get_smtencoding_nl_arith_repr ()  in
    uu____7632 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____7637  ->
    let uu____7638 = get_smtencoding_l_arith_repr ()  in
    uu____7638 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____7643  ->
    let uu____7644 = get_smtencoding_l_arith_repr ()  in
    uu____7644 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____7649  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____7654  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____7659  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____7664  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____7669  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____7674  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____7679  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____7684  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____7689  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____7694  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____7699  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____7704  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____7709  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____7714  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7721  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____7726  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____7739  ->
    let uu____7740 = get_using_facts_from ()  in
    match uu____7740 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7778  ->
    let uu____7779 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____7779
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7786  ->
    let uu____7787 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____7787 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7790 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7797  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____7802  ->
    let uu____7803 = get_smt ()  in
    match uu____7803 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7813  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____7818  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____7823  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7828  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____7833  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7838  ->
    (get_use_two_phase_tc ()) &&
      (let uu____7840 = lax ()  in Prims.op_Negation uu____7840)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7845  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7850  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7855  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7860  -> get_use_extracted_interfaces () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____7876 =
      let uu____7877 = trace_error ()  in Prims.op_Negation uu____7877  in
    if uu____7876
    then
      (push ();
       (try
          (fun uu___93_7882  ->
             match () with | () -> let retv = f ()  in (pop (); retv)) ()
        with | uu___92_7887 -> (pop (); FStar_Exn.raise uu___92_7887)))
    else (push (); (let retv = f ()  in pop (); retv))
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7899 = get_extract ()  in
    match uu____7899 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7910 =
            let uu____7923 = get_no_extract ()  in
            let uu____7926 = get_extract_namespace ()  in
            let uu____7929 = get_extract_module ()  in
            (uu____7923, uu____7926, uu____7929)  in
          match uu____7910 with
          | ([],[],[]) -> ()
          | uu____7944 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____7992,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____8011 -> false  in
          let uu____8020 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____8054  ->
                    match uu____8054 with
                    | (path,uu____8062) -> matches_path m_components path))
             in
          match uu____8020 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____8073,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____8093 = get_extract_namespace ()  in
          match uu____8093 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____8109 = get_extract_module ()  in
          match uu____8109 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____8121 = no_extract m1  in Prims.op_Negation uu____8121) &&
          (let uu____8123 =
             let uu____8132 = get_extract_namespace ()  in
             let uu____8135 = get_extract_module ()  in
             (uu____8132, uu____8135)  in
           (match uu____8123 with
            | ([],[]) -> true
            | uu____8146 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  