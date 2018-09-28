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
  fun uu___80_332  ->
    match uu___80_332 with
    | Bool b -> b
    | uu____334 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___81_339  ->
    match uu___81_339 with
    | Int b -> b
    | uu____341 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___82_346  ->
    match uu___82_346 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____349 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___83_356  ->
    match uu___83_356 with
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
    fun uu___84_417  ->
      match uu___84_417 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____421 = as_t v1  in FStar_Pervasives_Native.Some uu____421
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___85_428  ->
    match uu___85_428 with
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
  
let (internal_pop : unit -> Prims.bool) =
  fun uu____719  ->
    let curstack =
      let uu____723 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____723  in
    match curstack with
    | [] -> failwith "impossible: empty current option stack"
    | uu____757::[] -> false
    | uu____758::tl1 ->
        ((let uu____763 =
            let uu____768 =
              let uu____773 = FStar_ST.op_Bang fstar_options  in
              FStar_List.tl uu____773  in
            tl1 :: uu____768  in
          FStar_ST.op_Colon_Equals fstar_options uu____763);
         true)
  
let (internal_push : unit -> unit) =
  fun uu____840  ->
    let curstack =
      let uu____844 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____844  in
    let stack' =
      let uu____881 =
        let uu____882 = FStar_List.hd curstack  in
        FStar_Util.smap_copy uu____882  in
      uu____881 :: curstack  in
    let uu____885 =
      let uu____890 =
        let uu____895 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____895  in
      stack' :: uu____890  in
    FStar_ST.op_Colon_Equals fstar_options uu____885
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____963 = FStar_ST.op_Bang fstar_options  in
    match uu____963 with
    | [] -> failwith "set on empty option stack"
    | []::uu____997 -> failwith "set on empty current option stack"
    | (uu____1004::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
  
let (snapshot : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____1052  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____1076 = peek ()  in FStar_Util.smap_add uu____1076 k v1
  
let (set_option' :
  (Prims.string,option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____1087  -> match uu____1087 with | (k,v1) -> set_option k v1 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____1116 =
      let uu____1119 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____1119
       in
    FStar_ST.op_Colon_Equals light_off_files uu____1116
  
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
  fun uu____1590  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____1607  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____1672 =
      let uu____1675 = peek ()  in FStar_Util.smap_try_find uu____1675 s  in
    match uu____1672 with
    | FStar_Pervasives_Native.None  ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____1685 . Prims.string -> (option_val -> 'Auu____1685) -> 'Auu____1685
  = fun s  -> fun c  -> let uu____1701 = get_option s  in c uu____1701 
let (get_abort_on : unit -> Prims.int) =
  fun uu____1706  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1711  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1718  -> lookup_opt "admit_except" (as_option as_string) 
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1725  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1732  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1739  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____1744  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1751  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1760  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1769  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1778  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____1785  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1792  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1799  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1804  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____1809  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1816  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1823  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1828  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1837  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1850  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1859  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1866  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1871  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1876  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1883  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____1890  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____1895  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1902  -> lookup_opt "include" (as_list as_string) 
let (get_indent : unit -> Prims.bool) =
  fun uu____1909  -> lookup_opt "indent" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1914  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1919  -> lookup_opt "initial_ifuel" as_int 
let (get_lax : unit -> Prims.bool) =
  fun uu____1924  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1931  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1938  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____1943  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1948  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1953  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1958  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____1963  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____1968  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1973  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1980  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1987  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____1992  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1997  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____2002  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2009  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____2016  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2023  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____2030  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____2035  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____2040  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____2045  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____2050  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____2055  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____2060  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____2065  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____2070  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2077  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____2084  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2091  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____2098  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____2103  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____2108  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____2113  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____2118  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____2123  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____2128  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____2133  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____2138  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____2143  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____2148  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____2153  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____2158  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____2163  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____2168  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____2173  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____2178  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2185  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____2192  ->
    let uu____2193 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____2193
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2202  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2215  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____2224  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____2233  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____2240  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____2245  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____2252  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____2259  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____2264  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____2269  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____2274  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____2279  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____2284  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____2289  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string) =
  fun uu____2294  -> lookup_opt "warn_error" as_string 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____2299  -> lookup_opt "use_extracted_interfaces" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___86_2304  ->
    match uu___86_2304 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____2316 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____2322 = get_debug_level ()  in
    FStar_All.pipe_right uu____2322
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____2455  ->
    let uu____2456 =
      let uu____2457 = FStar_ST.op_Bang _version  in
      let uu____2477 = FStar_ST.op_Bang _platform  in
      let uu____2497 = FStar_ST.op_Bang _compiler  in
      let uu____2517 = FStar_ST.op_Bang _date  in
      let uu____2537 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2457
        uu____2477 uu____2497 uu____2517 uu____2537
       in
    FStar_Util.print_string uu____2456
  
let display_usage_aux :
  'Auu____2563 'Auu____2564 .
    ('Auu____2563,Prims.string,'Auu____2564 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2612  ->
         match uu____2612 with
         | (uu____2623,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2635 =
                      let uu____2636 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____2636  in
                    FStar_Util.print_string uu____2635
                  else
                    (let uu____2638 =
                       let uu____2639 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____2639 doc  in
                     FStar_Util.print_string uu____2638)
              | FStar_Getopt.OneArg (uu____2640,argname) ->
                  if doc = ""
                  then
                    let uu____2648 =
                      let uu____2649 = FStar_Util.colorize_bold flag  in
                      let uu____2650 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____2649 uu____2650
                       in
                    FStar_Util.print_string uu____2648
                  else
                    (let uu____2652 =
                       let uu____2653 = FStar_Util.colorize_bold flag  in
                       let uu____2654 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2653
                         uu____2654 doc
                        in
                     FStar_Util.print_string uu____2652))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char,Prims.string,option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____2682 = o  in
    match uu____2682 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2718 =
                let uu____2719 = f ()  in set_option name uu____2719  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____2734 = f x  in set_option name uu____2734
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____2754 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____2754  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let uu____2777 =
        let uu____2780 = lookup_opt name as_list'  in
        FStar_List.append uu____2780 [value]  in
      mk_list uu____2777
  
let accumulate_string :
  'Auu____2793 .
    Prims.string -> ('Auu____2793 -> Prims.string) -> 'Auu____2793 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____2814 =
          let uu____2815 =
            let uu____2816 = post_processor value  in mk_string uu____2816
             in
          accumulated_option name uu____2815  in
        set_option name uu____2814
  
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
    match projectee with | Const _0 -> true | uu____2912 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____2926 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____2939 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____2946 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____2960 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____2976 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____3002 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____3041 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val,opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____3076 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____3090 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____3111 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit,opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____3149 -> true
    | uu____3150 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____3157 -> uu____3157
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___91_3175  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____3177 ->
                      let uu____3178 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____3178 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____3182 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____3182
                  | PathStr uu____3185 -> mk_path str_val
                  | SimpleStr uu____3186 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____3191 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____3206 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____3206
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
            let uu____3225 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____3225
  
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
    | PostProcessed (uu____3262,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____3272,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____3299 = desc_of_opt_type typ  in
      match uu____3299 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____3305  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____3322 =
      let uu____3323 = as_string s  in FStar_String.lowercase uu____3323  in
    mk_string uu____3322
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char,Prims.string,opt_type,Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____3371  ->
    let uu____3383 =
      let uu____3395 =
        let uu____3407 =
          let uu____3419 =
            let uu____3429 =
              let uu____3430 = mk_bool true  in Const uu____3430  in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____3429,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
             in
          let uu____3432 =
            let uu____3444 =
              let uu____3456 =
                let uu____3466 =
                  let uu____3467 = mk_bool true  in Const uu____3467  in
                (FStar_Getopt.noshort, "cache_off", uu____3466,
                  "Do not read or write any .checked files")
                 in
              let uu____3469 =
                let uu____3481 =
                  let uu____3491 =
                    let uu____3492 = mk_bool true  in Const uu____3492  in
                  (FStar_Getopt.noshort, "cmi", uu____3491,
                    "Inline across module interfaces during extraction (aka. cross-module inlining)")
                   in
                let uu____3494 =
                  let uu____3506 =
                    let uu____3518 =
                      let uu____3530 =
                        let uu____3542 =
                          let uu____3554 =
                            let uu____3566 =
                              let uu____3578 =
                                let uu____3588 =
                                  let uu____3589 = mk_bool true  in
                                  Const uu____3589  in
                                (FStar_Getopt.noshort, "detail_errors",
                                  uu____3588,
                                  "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                 in
                              let uu____3591 =
                                let uu____3603 =
                                  let uu____3613 =
                                    let uu____3614 = mk_bool true  in
                                    Const uu____3614  in
                                  (FStar_Getopt.noshort,
                                    "detail_hint_replay", uu____3613,
                                    "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                   in
                                let uu____3616 =
                                  let uu____3628 =
                                    let uu____3638 =
                                      let uu____3639 = mk_bool true  in
                                      Const uu____3639  in
                                    (FStar_Getopt.noshort, "doc", uu____3638,
                                      "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                     in
                                  let uu____3641 =
                                    let uu____3653 =
                                      let uu____3665 =
                                        let uu____3675 =
                                          let uu____3676 = mk_bool true  in
                                          Const uu____3676  in
                                        (FStar_Getopt.noshort,
                                          "eager_inference", uu____3675,
                                          "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                         in
                                      let uu____3678 =
                                        let uu____3690 =
                                          let uu____3700 =
                                            let uu____3701 = mk_bool true  in
                                            Const uu____3701  in
                                          (FStar_Getopt.noshort,
                                            "eager_subtyping", uu____3700,
                                            "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                           in
                                        let uu____3703 =
                                          let uu____3715 =
                                            let uu____3727 =
                                              let uu____3739 =
                                                let uu____3751 =
                                                  let uu____3761 =
                                                    let uu____3762 =
                                                      mk_bool true  in
                                                    Const uu____3762  in
                                                  (FStar_Getopt.noshort,
                                                    "expose_interfaces",
                                                    uu____3761,
                                                    "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                   in
                                                let uu____3764 =
                                                  let uu____3776 =
                                                    let uu____3786 =
                                                      let uu____3787 =
                                                        mk_bool true  in
                                                      Const uu____3787  in
                                                    (FStar_Getopt.noshort,
                                                      "hide_uvar_nums",
                                                      uu____3786,
                                                      "Don't print unification variable numbers")
                                                     in
                                                  let uu____3789 =
                                                    let uu____3801 =
                                                      let uu____3813 =
                                                        let uu____3823 =
                                                          let uu____3824 =
                                                            mk_bool true  in
                                                          Const uu____3824
                                                           in
                                                        (FStar_Getopt.noshort,
                                                          "hint_info",
                                                          uu____3823,
                                                          "Print information regarding hints (deprecated; use --query_stats instead)")
                                                         in
                                                      let uu____3826 =
                                                        let uu____3838 =
                                                          let uu____3848 =
                                                            let uu____3849 =
                                                              mk_bool true
                                                               in
                                                            Const uu____3849
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "in", uu____3848,
                                                            "Legacy interactive mode; reads input from stdin")
                                                           in
                                                        let uu____3851 =
                                                          let uu____3863 =
                                                            let uu____3873 =
                                                              let uu____3874
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____3874
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "ide",
                                                              uu____3873,
                                                              "JSON-based interactive mode for IDEs")
                                                             in
                                                          let uu____3876 =
                                                            let uu____3888 =
                                                              let uu____3900
                                                                =
                                                                let uu____3910
                                                                  =
                                                                  let uu____3911
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                  Const
                                                                    uu____3911
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "indent",
                                                                  uu____3910,
                                                                  "Parses and outputs the files on the command line")
                                                                 in
                                                              let uu____3913
                                                                =
                                                                let uu____3925
                                                                  =
                                                                  let uu____3937
                                                                    =
                                                                    let uu____3949
                                                                    =
                                                                    let uu____3959
                                                                    =
                                                                    let uu____3960
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3960
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3959,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____3962
                                                                    =
                                                                    let uu____3974
                                                                    =
                                                                    let uu____3986
                                                                    =
                                                                    let uu____3996
                                                                    =
                                                                    let uu____3997
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____3997
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3996,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____3999
                                                                    =
                                                                    let uu____4011
                                                                    =
                                                                    let uu____4021
                                                                    =
                                                                    let uu____4022
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4022
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____4021,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____4024
                                                                    =
                                                                    let uu____4036
                                                                    =
                                                                    let uu____4048
                                                                    =
                                                                    let uu____4060
                                                                    =
                                                                    let uu____4072
                                                                    =
                                                                    let uu____4082
                                                                    =
                                                                    let uu____4083
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4083
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____4082,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____4085
                                                                    =
                                                                    let uu____4097
                                                                    =
                                                                    let uu____4109
                                                                    =
                                                                    let uu____4119
                                                                    =
                                                                    let uu____4120
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4120
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____4119,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____4122
                                                                    =
                                                                    let uu____4134
                                                                    =
                                                                    let uu____4146
                                                                    =
                                                                    let uu____4156
                                                                    =
                                                                    let uu____4157
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4157
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____4156,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____4159
                                                                    =
                                                                    let uu____4171
                                                                    =
                                                                    let uu____4181
                                                                    =
                                                                    let uu____4182
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4182
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____4181,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____4184
                                                                    =
                                                                    let uu____4196
                                                                    =
                                                                    let uu____4206
                                                                    =
                                                                    let uu____4207
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4207
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____4206,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____4209
                                                                    =
                                                                    let uu____4221
                                                                    =
                                                                    let uu____4233
                                                                    =
                                                                    let uu____4245
                                                                    =
                                                                    let uu____4255
                                                                    =
                                                                    let uu____4256
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4256
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____4255,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____4258
                                                                    =
                                                                    let uu____4270
                                                                    =
                                                                    let uu____4280
                                                                    =
                                                                    let uu____4281
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4281
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____4280,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____4283
                                                                    =
                                                                    let uu____4295
                                                                    =
                                                                    let uu____4305
                                                                    =
                                                                    let uu____4306
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4306
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____4305,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____4308
                                                                    =
                                                                    let uu____4320
                                                                    =
                                                                    let uu____4330
                                                                    =
                                                                    let uu____4331
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4331
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____4330,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____4333
                                                                    =
                                                                    let uu____4345
                                                                    =
                                                                    let uu____4355
                                                                    =
                                                                    let uu____4356
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4356
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____4355,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____4358
                                                                    =
                                                                    let uu____4370
                                                                    =
                                                                    let uu____4380
                                                                    =
                                                                    let uu____4381
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4381
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____4380,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)")
                                                                     in
                                                                    let uu____4383
                                                                    =
                                                                    let uu____4395
                                                                    =
                                                                    let uu____4405
                                                                    =
                                                                    let uu____4406
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4406
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____4405,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____4408
                                                                    =
                                                                    let uu____4420
                                                                    =
                                                                    let uu____4430
                                                                    =
                                                                    let uu____4431
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4431
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____4430,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____4433
                                                                    =
                                                                    let uu____4445
                                                                    =
                                                                    let uu____4455
                                                                    =
                                                                    let uu____4456
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4456
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____4455,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____4458
                                                                    =
                                                                    let uu____4470
                                                                    =
                                                                    let uu____4482
                                                                    =
                                                                    let uu____4492
                                                                    =
                                                                    let uu____4493
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4493
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4492,
                                                                    " ")  in
                                                                    let uu____4495
                                                                    =
                                                                    let uu____4507
                                                                    =
                                                                    let uu____4519
                                                                    =
                                                                    let uu____4531
                                                                    =
                                                                    let uu____4543
                                                                    =
                                                                    let uu____4555
                                                                    =
                                                                    let uu____4565
                                                                    =
                                                                    let uu____4566
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4566
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4565,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____4568
                                                                    =
                                                                    let uu____4580
                                                                    =
                                                                    let uu____4590
                                                                    =
                                                                    let uu____4591
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4591
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____4590,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____4593
                                                                    =
                                                                    let uu____4605
                                                                    =
                                                                    let uu____4615
                                                                    =
                                                                    let uu____4616
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4616
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____4615,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____4618
                                                                    =
                                                                    let uu____4630
                                                                    =
                                                                    let uu____4640
                                                                    =
                                                                    let uu____4641
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4641
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4640,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____4643
                                                                    =
                                                                    let uu____4655
                                                                    =
                                                                    let uu____4667
                                                                    =
                                                                    let uu____4677
                                                                    =
                                                                    let uu____4678
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4678
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____4677,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____4680
                                                                    =
                                                                    let uu____4692
                                                                    =
                                                                    let uu____4704
                                                                    =
                                                                    let uu____4714
                                                                    =
                                                                    let uu____4715
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4715
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4714,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____4717
                                                                    =
                                                                    let uu____4729
                                                                    =
                                                                    let uu____4739
                                                                    =
                                                                    let uu____4740
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4740
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4739,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____4742
                                                                    =
                                                                    let uu____4754
                                                                    =
                                                                    let uu____4764
                                                                    =
                                                                    let uu____4765
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4765
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4764,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____4767
                                                                    =
                                                                    let uu____4779
                                                                    =
                                                                    let uu____4789
                                                                    =
                                                                    let uu____4790
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4790
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4789,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____4792
                                                                    =
                                                                    let uu____4804
                                                                    =
                                                                    let uu____4814
                                                                    =
                                                                    let uu____4815
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4815
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4814,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____4817
                                                                    =
                                                                    let uu____4829
                                                                    =
                                                                    let uu____4839
                                                                    =
                                                                    let uu____4840
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4840
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4839,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____4842
                                                                    =
                                                                    let uu____4854
                                                                    =
                                                                    let uu____4864
                                                                    =
                                                                    let uu____4865
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4865
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4864,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____4867
                                                                    =
                                                                    let uu____4879
                                                                    =
                                                                    let uu____4889
                                                                    =
                                                                    let uu____4890
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4890
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4889,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____4892
                                                                    =
                                                                    let uu____4904
                                                                    =
                                                                    let uu____4916
                                                                    =
                                                                    let uu____4926
                                                                    =
                                                                    let uu____4927
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4927
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____4926,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____4929
                                                                    =
                                                                    let uu____4941
                                                                    =
                                                                    let uu____4951
                                                                    =
                                                                    let uu____4952
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____4952
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4951,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____4954
                                                                    =
                                                                    let uu____4966
                                                                    =
                                                                    let uu____4978
                                                                    =
                                                                    let uu____4990
                                                                    =
                                                                    let uu____5002
                                                                    =
                                                                    let uu____5012
                                                                    =
                                                                    let uu____5013
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5013
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____5012,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____5015
                                                                    =
                                                                    let uu____5027
                                                                    =
                                                                    let uu____5037
                                                                    =
                                                                    let uu____5038
                                                                    =
                                                                    let uu____5046
                                                                    =
                                                                    let uu____5047
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5047
                                                                     in
                                                                    ((fun
                                                                    uu____5053
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____5046)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____5038
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____5037,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____5057
                                                                    =
                                                                    let uu____5069
                                                                    =
                                                                    let uu____5079
                                                                    =
                                                                    let uu____5080
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5080
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____5079,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____5082
                                                                    =
                                                                    let uu____5094
                                                                    =
                                                                    let uu____5106
                                                                    =
                                                                    let uu____5116
                                                                    =
                                                                    let uu____5117
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5117
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____5116,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____5119
                                                                    =
                                                                    let uu____5131
                                                                    =
                                                                    let uu____5143
                                                                    =
                                                                    let uu____5155
                                                                    =
                                                                    let uu____5167
                                                                    =
                                                                    let uu____5179
                                                                    =
                                                                    let uu____5189
                                                                    =
                                                                    let uu____5190
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5190
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____5189,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____5192
                                                                    =
                                                                    let uu____5204
                                                                    =
                                                                    let uu____5214
                                                                    =
                                                                    let uu____5215
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5215
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____5214,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____5217
                                                                    =
                                                                    let uu____5229
                                                                    =
                                                                    let uu____5241
                                                                    =
                                                                    let uu____5253
                                                                    =
                                                                    let uu____5263
                                                                    =
                                                                    let uu____5264
                                                                    =
                                                                    let uu____5272
                                                                    =
                                                                    let uu____5273
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5273
                                                                     in
                                                                    ((fun
                                                                    uu____5278
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____5272)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____5264
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____5263,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____5299
                                                                    =
                                                                    let uu____5311
                                                                    =
                                                                    let uu____5321
                                                                    =
                                                                    let uu____5322
                                                                    =
                                                                    let uu____5330
                                                                    =
                                                                    let uu____5331
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5331
                                                                     in
                                                                    ((fun
                                                                    uu____5336
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____5330)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____5322
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____5321,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____5357
                                                                    =
                                                                    let uu____5369
                                                                    =
                                                                    let uu____5379
                                                                    =
                                                                    let uu____5380
                                                                    =
                                                                    let uu____5388
                                                                    =
                                                                    let uu____5389
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5389
                                                                     in
                                                                    ((fun
                                                                    uu____5395
                                                                     ->
                                                                    (
                                                                    let uu____5397
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____5397);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____5388)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____5380
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____5379,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____5369]
                                                                     in
                                                                    uu____5311
                                                                    ::
                                                                    uu____5357
                                                                     in
                                                                    uu____5253
                                                                    ::
                                                                    uu____5299
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____5241
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____5229
                                                                     in
                                                                    uu____5204
                                                                    ::
                                                                    uu____5217
                                                                     in
                                                                    uu____5179
                                                                    ::
                                                                    uu____5192
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____5167
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____5155
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____5143
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____5131
                                                                     in
                                                                    uu____5106
                                                                    ::
                                                                    uu____5119
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____5094
                                                                     in
                                                                    uu____5069
                                                                    ::
                                                                    uu____5082
                                                                     in
                                                                    uu____5027
                                                                    ::
                                                                    uu____5057
                                                                     in
                                                                    uu____5002
                                                                    ::
                                                                    uu____5015
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4990
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4978
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4966
                                                                     in
                                                                    uu____4941
                                                                    ::
                                                                    uu____4954
                                                                     in
                                                                    uu____4916
                                                                    ::
                                                                    uu____4929
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4904
                                                                     in
                                                                    uu____4879
                                                                    ::
                                                                    uu____4892
                                                                     in
                                                                    uu____4854
                                                                    ::
                                                                    uu____4867
                                                                     in
                                                                    uu____4829
                                                                    ::
                                                                    uu____4842
                                                                     in
                                                                    uu____4804
                                                                    ::
                                                                    uu____4817
                                                                     in
                                                                    uu____4779
                                                                    ::
                                                                    uu____4792
                                                                     in
                                                                    uu____4754
                                                                    ::
                                                                    uu____4767
                                                                     in
                                                                    uu____4729
                                                                    ::
                                                                    uu____4742
                                                                     in
                                                                    uu____4704
                                                                    ::
                                                                    uu____4717
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____4692
                                                                     in
                                                                    uu____4667
                                                                    ::
                                                                    uu____4680
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4655
                                                                     in
                                                                    uu____4630
                                                                    ::
                                                                    uu____4643
                                                                     in
                                                                    uu____4605
                                                                    ::
                                                                    uu____4618
                                                                     in
                                                                    uu____4580
                                                                    ::
                                                                    uu____4593
                                                                     in
                                                                    uu____4555
                                                                    ::
                                                                    uu____4568
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4543
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4531
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4519
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4507
                                                                     in
                                                                    uu____4482
                                                                    ::
                                                                    uu____4495
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____4470
                                                                     in
                                                                    uu____4445
                                                                    ::
                                                                    uu____4458
                                                                     in
                                                                    uu____4420
                                                                    ::
                                                                    uu____4433
                                                                     in
                                                                    uu____4395
                                                                    ::
                                                                    uu____4408
                                                                     in
                                                                    uu____4370
                                                                    ::
                                                                    uu____4383
                                                                     in
                                                                    uu____4345
                                                                    ::
                                                                    uu____4358
                                                                     in
                                                                    uu____4320
                                                                    ::
                                                                    uu____4333
                                                                     in
                                                                    uu____4295
                                                                    ::
                                                                    uu____4308
                                                                     in
                                                                    uu____4270
                                                                    ::
                                                                    uu____4283
                                                                     in
                                                                    uu____4245
                                                                    ::
                                                                    uu____4258
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____4233
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____4221
                                                                     in
                                                                    uu____4196
                                                                    ::
                                                                    uu____4209
                                                                     in
                                                                    uu____4171
                                                                    ::
                                                                    uu____4184
                                                                     in
                                                                    uu____4146
                                                                    ::
                                                                    uu____4159
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____4134
                                                                     in
                                                                    uu____4109
                                                                    ::
                                                                    uu____4122
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____4097
                                                                     in
                                                                    uu____4072
                                                                    ::
                                                                    uu____4085
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____4060
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____4048
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____4036
                                                                     in
                                                                    uu____4011
                                                                    ::
                                                                    uu____4024
                                                                     in
                                                                    uu____3986
                                                                    ::
                                                                    uu____3999
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3974
                                                                     in
                                                                    uu____3949
                                                                    ::
                                                                    uu____3962
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (
                                                                    IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____3937
                                                                   in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_fuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of recursive functions to try initially (default 2)")
                                                                  ::
                                                                  uu____3925
                                                                 in
                                                              uu____3900 ::
                                                                uu____3913
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "include",
                                                              (ReverseAccumulated
                                                                 (PathStr
                                                                    "path")),
                                                              "A directory in which to search for files included on the command line")
                                                              :: uu____3888
                                                             in
                                                          uu____3863 ::
                                                            uu____3876
                                                           in
                                                        uu____3838 ::
                                                          uu____3851
                                                         in
                                                      uu____3813 ::
                                                        uu____3826
                                                       in
                                                    (FStar_Getopt.noshort,
                                                      "hint_file",
                                                      (PathStr "path"),
                                                      "Read/write hints to <path> (instead of module-specific hints files)")
                                                      :: uu____3801
                                                     in
                                                  uu____3776 :: uu____3789
                                                   in
                                                uu____3751 :: uu____3764  in
                                              (FStar_Getopt.noshort,
                                                "extract_namespace",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "namespace name")))),
                                                "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                :: uu____3739
                                               in
                                            (FStar_Getopt.noshort,
                                              "extract_module",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "module_name")))),
                                              "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                              :: uu____3727
                                             in
                                          (FStar_Getopt.noshort, "extract",
                                            (Accumulated
                                               (SimpleStr
                                                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                            "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                            :: uu____3715
                                           in
                                        uu____3690 :: uu____3703  in
                                      uu____3665 :: uu____3678  in
                                    (FStar_Getopt.noshort, "dump_module",
                                      (Accumulated (SimpleStr "module_name")),
                                      "") :: uu____3653
                                     in
                                  uu____3628 :: uu____3641  in
                                uu____3603 :: uu____3616  in
                              uu____3578 :: uu____3591  in
                            (FStar_Getopt.noshort, "dep",
                              (EnumStr ["make"; "graph"; "full"; "raw"]),
                              "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                              :: uu____3566
                             in
                          (FStar_Getopt.noshort, "defensive",
                            (EnumStr ["no"; "warn"; "fail"]),
                            "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                            :: uu____3554
                           in
                        (FStar_Getopt.noshort, "debug_level",
                          (Accumulated
                             (OpenEnumStr
                                (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                          "Control the verbosity of debugging info") ::
                          uu____3542
                         in
                      (FStar_Getopt.noshort, "debug",
                        (Accumulated (SimpleStr "module_name")),
                        "Print lots of debugging information while checking module")
                        :: uu____3530
                       in
                    (FStar_Getopt.noshort, "codegen-lib",
                      (Accumulated (SimpleStr "namespace")),
                      "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                      :: uu____3518
                     in
                  (FStar_Getopt.noshort, "codegen",
                    (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                    "Generate code for further compilation to executable code, or build a compiler plugin")
                    :: uu____3506
                   in
                uu____3481 :: uu____3494  in
              uu____3456 :: uu____3469  in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____3444
             in
          uu____3419 :: uu____3432  in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____3407
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____3395
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___87_6387  ->
             match uu___87_6387 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____3383

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____6410  ->
    let uu____6413 = specs_with_types ()  in
    FStar_List.map
      (fun uu____6440  ->
         match uu____6440 with
         | (short,long,typ,doc) ->
             let uu____6456 =
               let uu____6468 = arg_spec_of_opt_type long typ  in
               (short, long, uu____6468, doc)  in
             mk_spec uu____6456) uu____6413

let (settable : Prims.string -> Prims.bool) =
  fun uu___88_6478  ->
    match uu___88_6478 with
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
    | uu____6479 -> false
  
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
       (fun uu____6553  ->
          match uu____6553 with
          | (uu____6565,x,uu____6567,uu____6568) -> settable x))
  
let (resettable_specs :
  (FStar_BaseTypes.char,Prims.string,unit FStar_Getopt.opt_variant,Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____6630  ->
          match uu____6630 with
          | (uu____6642,x,uu____6644,uu____6645) -> resettable x))
  
let (display_usage : unit -> unit) =
  fun uu____6656  ->
    let uu____6657 = specs ()  in display_usage_aux uu____6657
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____6681 -> true
    | uu____6682 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____6689 -> uu____6689
  
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
        (fun uu___93_6706  ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____6717 =
            FStar_Util.format1 "File %s is not a valid option" s1  in
          FStar_Getopt.Error uu____6717
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____6745  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____6750 =
             let uu____6753 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____6753 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____6750)
       in
    let uu____6802 =
      let uu____6805 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6805
       in
    (res, uu____6802)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6839  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____6874 = specs ()  in
       FStar_Getopt.parse_cmdline uu____6874 (fun x  -> ())  in
     (let uu____6880 =
        let uu____6885 =
          let uu____6886 = FStar_List.map mk_string old_verify_module  in
          List uu____6886  in
        ("verify_module", uu____6885)  in
      set_option' uu____6880);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____6896 =
        let uu____6897 =
          let uu____6898 =
            let uu____6899 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____6899  in
          (FStar_String.length f1) - uu____6898  in
        uu____6897 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6896  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6905 = get_lax ()  in
    if uu____6905
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____6915 = module_name_of_file_name fn  in should_verify uu____6915
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6921 = get___temp_no_proj ()  in
    FStar_List.contains m uu____6921
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____6929 = should_verify m  in
    if uu____6929 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6937  ->
    let uu____6938 = get_no_default_includes ()  in
    if uu____6938
    then get_include ()
    else
      (let lib_paths =
         let uu____6945 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____6945 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.."  in
             let defs = universe_include_path_base_dirs  in
             let uu____6954 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> Prims.strcat fstar_home x))
                in
             FStar_All.pipe_right uu____6954
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____6968 =
         let uu____6971 = get_include ()  in
         FStar_List.append uu____6971 ["."]  in
       FStar_List.append lib_paths uu____6968)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____6984 = FStar_Util.smap_try_find file_map filename  in
    match uu____6984 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___95_6997  ->
               match () with
               | () ->
                   let uu____7000 = FStar_Util.is_path_absolute filename  in
                   if uu____7000
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____7007 =
                        let uu____7010 = include_path ()  in
                        FStar_List.rev uu____7010  in
                      FStar_Util.find_map uu____7007
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___94_7022 -> FStar_Pervasives_Native.None  in
        (match result with
         | FStar_Pervasives_Native.None  -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
  
let (prims : unit -> Prims.string) =
  fun uu____7033  ->
    let uu____7034 = get_prims ()  in
    match uu____7034 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____7038 = find_file filename  in
        (match uu____7038 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____7042 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____7042)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____7048  ->
    let uu____7049 = prims ()  in FStar_Util.basename uu____7049
  
let (pervasives : unit -> Prims.string) =
  fun uu____7054  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____7056 = find_file filename  in
    match uu____7056 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____7060 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____7060
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____7065  ->
    let uu____7066 = pervasives ()  in FStar_Util.basename uu____7066
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____7071  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____7073 = find_file filename  in
    match uu____7073 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____7077 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____7077
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____7083 = get_odir ()  in
    match uu____7083 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____7092 = get_cache_dir ()  in
    match uu____7092 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____7096 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____7096
  
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
             let uu____7162 =
               FStar_Util.substring_from s (Prims.parse_int "1")  in
             path_of_text uu____7162  in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s  in
           ((path_of_text s1), true))
       in
    let uu____7170 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting)))
       in
    FStar_All.pipe_right uu____7170 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____7240 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____7240 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____7249  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____7254  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7261  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____7266  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____7271  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____7276  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____7282 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____7288 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____7294 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____7300 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____7307  ->
    let uu____7308 = get_codegen ()  in
    FStar_Util.map_opt uu____7308
      (fun uu___89_7312  ->
         match uu___89_7312 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____7313 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____7322  ->
    let uu____7323 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____7323
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____7340  -> let uu____7341 = get_debug ()  in uu____7341 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____7351 = get_debug ()  in
    FStar_All.pipe_right uu____7351 (FStar_List.contains modul)
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____7368 = get_debug ()  in
       FStar_All.pipe_right uu____7368 (FStar_List.contains modul)) &&
        (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____7377  -> let uu____7378 = get_defensive ()  in uu____7378 <> "no" 
let (defensive_fail : unit -> Prims.bool) =
  fun uu____7383  ->
    let uu____7384 = get_defensive ()  in uu____7384 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7391  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____7396  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____7401  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____7406  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____7412 = get_dump_module ()  in
    FStar_All.pipe_right uu____7412 (FStar_List.contains s)
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____7421  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____7426  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____7432 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____7432
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____7462  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____7467  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____7472  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7479  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____7484  -> get_ide () 
let (indent : unit -> Prims.bool) = fun uu____7489  -> get_indent () 
let (initial_fuel : unit -> Prims.int) =
  fun uu____7494  ->
    let uu____7495 = get_initial_fuel ()  in
    let uu____7496 = get_max_fuel ()  in Prims.min uu____7495 uu____7496
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____7501  ->
    let uu____7502 = get_initial_ifuel ()  in
    let uu____7503 = get_max_ifuel ()  in Prims.min uu____7502 uu____7503
  
let (interactive : unit -> Prims.bool) =
  fun uu____7508  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____7513  -> get_lax () 
let (load : unit -> Prims.string Prims.list) = fun uu____7520  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____7525  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____7530  -> get_log_queries () 
let (log_types : unit -> Prims.bool) = fun uu____7535  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____7540  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____7545  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____7550  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____7555  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____7560  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____7565  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____7570  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let s1 = FStar_String.lowercase s  in
    let uu____7577 = get_no_extract ()  in
    FStar_All.pipe_right uu____7577
      (FStar_Util.for_some (fun f  -> (FStar_String.lowercase f) = s1))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____7588  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____7593  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____7598  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____7603  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7610  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____7615  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____7620  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____7625  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____7630  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____7635  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____7640  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____7645  -> (get_print_z3_statistics ()) || (get_query_stats ()) 
let (query_stats : unit -> Prims.bool) =
  fun uu____7650  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____7655  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7662  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____7667  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____7672  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____7677  ->
    let uu____7678 = get_smtencoding_nl_arith_repr ()  in
    uu____7678 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____7683  ->
    let uu____7684 = get_smtencoding_nl_arith_repr ()  in
    uu____7684 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____7689  ->
    let uu____7690 = get_smtencoding_nl_arith_repr ()  in
    uu____7690 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____7695  ->
    let uu____7696 = get_smtencoding_l_arith_repr ()  in
    uu____7696 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____7701  ->
    let uu____7702 = get_smtencoding_l_arith_repr ()  in
    uu____7702 = "boxwrap"
  
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____7707  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____7712  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____7717  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____7722  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____7727  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____7732  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____7737  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____7742  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____7747  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____7752  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____7757  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____7762  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____7767  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____7772  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7779  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____7784  -> get_use_tactics () 
let (using_facts_from :
  unit ->
    (Prims.string Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____7797  ->
    let uu____7798 = get_using_facts_from ()  in
    match uu____7798 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7836  ->
    let uu____7837 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____7837
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7844  ->
    let uu____7845 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____7845 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7848 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7855  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____7860  ->
    let uu____7861 = get_smt ()  in
    match uu____7861 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7871  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____7876  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____7881  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7886  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____7891  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7896  ->
    (get_use_two_phase_tc ()) &&
      (let uu____7898 = lax ()  in Prims.op_Negation uu____7898)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____7903  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7908  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____7913  -> get_warn_error () 
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7918  -> get_use_extracted_interfaces () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____7934 =
      let uu____7935 = trace_error ()  in Prims.op_Negation uu____7935  in
    if uu____7934
    then
      (push ();
       (let r =
          try
            (fun uu___97_7948  ->
               match () with
               | () -> let uu____7953 = f ()  in FStar_Util.Inr uu____7953)
              ()
          with | uu___96_7955 -> FStar_Util.Inl uu___96_7955  in
        pop ();
        (match r with
         | FStar_Util.Inr v1 -> v1
         | FStar_Util.Inl ex -> FStar_Exn.raise ex)))
    else (push (); (let retv = f ()  in pop (); retv))
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____7973 = get_extract ()  in
    match uu____7973 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7984 =
            let uu____7997 = get_no_extract ()  in
            let uu____8000 = get_extract_namespace ()  in
            let uu____8003 = get_extract_module ()  in
            (uu____7997, uu____8000, uu____8003)  in
          match uu____7984 with
          | ([],[],[]) -> ()
          | uu____8018 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting  in
          let m_components = path_of_text m1  in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____8066,[]) -> true
            | (m2::ms,p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____8085 -> false  in
          let uu____8094 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____8128  ->
                    match uu____8128 with
                    | (path,uu____8136) -> matches_path m_components path))
             in
          match uu____8094 with
          | FStar_Pervasives_Native.None  -> false
          | FStar_Pervasives_Native.Some (uu____8147,flag) -> flag))
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____8167 = get_extract_namespace ()  in
          match uu____8167 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____8183 = get_extract_module ()  in
          match uu____8183 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____8195 = no_extract m1  in Prims.op_Negation uu____8195) &&
          (let uu____8197 =
             let uu____8206 = get_extract_namespace ()  in
             let uu____8209 = get_extract_module ()  in
             (uu____8206, uu____8209)  in
           (match uu____8197 with
            | ([],[]) -> true
            | uu____8220 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  