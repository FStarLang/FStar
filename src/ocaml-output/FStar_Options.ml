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
  fun projectee -> match projectee with | Low -> true | uu____59 -> false
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee -> match projectee with | Medium -> true | uu____65 -> false
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee -> match projectee with | High -> true | uu____71 -> false
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee -> match projectee with | Extreme -> true | uu____77 -> false
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Other _0 -> true | uu____84 -> false
let (__proj__Other__item___0 : debug_level_t -> Prims.string) =
  fun projectee -> match projectee with | Other _0 -> _0
type option_val =
  | Bool of Prims.bool 
  | String of Prims.string 
  | Path of Prims.string 
  | Int of Prims.int 
  | List of option_val Prims.list 
  | Unset 
let (uu___is_Bool : option_val -> Prims.bool) =
  fun projectee ->
    match projectee with | Bool _0 -> true | uu____125 -> false
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee -> match projectee with | Bool _0 -> _0
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee ->
    match projectee with | String _0 -> true | uu____139 -> false
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee -> match projectee with | String _0 -> _0
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee ->
    match projectee with | Path _0 -> true | uu____153 -> false
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee -> match projectee with | Path _0 -> _0
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee -> match projectee with | Int _0 -> true | uu____167 -> false
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee -> match projectee with | Int _0 -> _0
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee ->
    match projectee with | List _0 -> true | uu____183 -> false
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee -> match projectee with | List _0 -> _0
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee -> match projectee with | Unset -> true | uu____202 -> false
let (mk_bool : Prims.bool -> option_val) = fun _0_4 -> Bool _0_4
let (mk_string : Prims.string -> option_val) = fun _0_5 -> String _0_5
let (mk_path : Prims.string -> option_val) = fun _0_6 -> Path _0_6
let (mk_int : Prims.int -> option_val) = fun _0_7 -> Int _0_7
let (mk_list : option_val Prims.list -> option_val) = fun _0_8 -> List _0_8
type options =
  | Set 
  | Reset 
  | Restore 
let (uu___is_Set : options -> Prims.bool) =
  fun projectee -> match projectee with | Set -> true | uu____230 -> false
let (uu___is_Reset : options -> Prims.bool) =
  fun projectee -> match projectee with | Reset -> true | uu____236 -> false
let (uu___is_Restore : options -> Prims.bool) =
  fun projectee ->
    match projectee with | Restore -> true | uu____242 -> false
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false
let (__unit_tests : unit -> Prims.bool) =
  fun uu____260 -> FStar_ST.op_Bang __unit_tests__
let (__set_unit_tests : unit -> unit) =
  fun uu____284 -> FStar_ST.op_Colon_Equals __unit_tests__ true
let (__clear_unit_tests : unit -> unit) =
  fun uu____308 -> FStar_ST.op_Colon_Equals __unit_tests__ false
let (as_bool : option_val -> Prims.bool) =
  fun uu___76_332 ->
    match uu___76_332 with
    | Bool b -> b
    | uu____334 -> failwith "Impos: expected Bool"
let (as_int : option_val -> Prims.int) =
  fun uu___77_339 ->
    match uu___77_339 with
    | Int b -> b
    | uu____341 -> failwith "Impos: expected Int"
let (as_string : option_val -> Prims.string) =
  fun uu___78_346 ->
    match uu___78_346 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____349 -> failwith "Impos: expected String"
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___79_356 ->
    match uu___79_356 with
    | List ts -> ts
    | uu____362 -> failwith "Impos: expected List"
let as_list :
  'Auu____371 .
    (option_val -> 'Auu____371) -> option_val -> 'Auu____371 Prims.list
  =
  fun as_t ->
    fun x ->
      let uu____389 = as_list' x in
      FStar_All.pipe_right uu____389 (FStar_List.map as_t)
let as_option :
  'Auu____402 .
    (option_val -> 'Auu____402) ->
      option_val -> 'Auu____402 FStar_Pervasives_Native.option
  =
  fun as_t ->
    fun uu___80_417 ->
      match uu___80_417 with
      | Unset -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____421 = as_t v1 in FStar_Pervasives_Native.Some uu____421
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___81_428 ->
    match uu___81_428 with
    | List ls ->
        let uu____434 =
          FStar_List.map
            (fun l ->
               let uu____444 = as_string l in FStar_Util.split uu____444 ",")
            ls in
        FStar_All.pipe_left FStar_List.flatten uu____434
    | uu____451 -> failwith "Impos: expected String (comma list)"
type optionstate = option_val FStar_Util.smap
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref []
let (peek : unit -> optionstate) =
  fun uu____483 ->
    let uu____484 =
      let uu____487 = FStar_ST.op_Bang fstar_options in
      FStar_List.hd uu____487 in
    FStar_List.hd uu____484
let (pop : unit -> unit) =
  fun uu____525 ->
    let uu____526 = FStar_ST.op_Bang fstar_options in
    match uu____526 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____560::[] -> failwith "TOO MANY POPS!"
    | uu____567::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
let (push : unit -> unit) =
  fun uu____608 ->
    let uu____609 =
      let uu____614 =
        let uu____617 =
          let uu____620 = FStar_ST.op_Bang fstar_options in
          FStar_List.hd uu____620 in
        FStar_List.map FStar_Util.smap_copy uu____617 in
      let uu____654 = FStar_ST.op_Bang fstar_options in uu____614 ::
        uu____654 in
    FStar_ST.op_Colon_Equals fstar_options uu____609
let (internal_pop : unit -> Prims.bool) =
  fun uu____719 ->
    let curstack =
      let uu____723 = FStar_ST.op_Bang fstar_options in
      FStar_List.hd uu____723 in
    match curstack with
    | [] -> failwith "impossible: empty current option stack"
    | uu____757::[] -> false
    | uu____758::tl1 ->
        ((let uu____763 =
            let uu____768 =
              let uu____773 = FStar_ST.op_Bang fstar_options in
              FStar_List.tl uu____773 in
            tl1 :: uu____768 in
          FStar_ST.op_Colon_Equals fstar_options uu____763);
         true)
let (internal_push : unit -> unit) =
  fun uu____840 ->
    let curstack =
      let uu____844 = FStar_ST.op_Bang fstar_options in
      FStar_List.hd uu____844 in
    let stack' =
      let uu____881 =
        let uu____882 = FStar_List.hd curstack in
        FStar_Util.smap_copy uu____882 in
      uu____881 :: curstack in
    let uu____885 =
      let uu____890 =
        let uu____895 = FStar_ST.op_Bang fstar_options in
        FStar_List.tl uu____895 in
      stack' :: uu____890 in
    FStar_ST.op_Colon_Equals fstar_options uu____885
let (set : optionstate -> unit) =
  fun o ->
    let uu____963 = FStar_ST.op_Bang fstar_options in
    match uu____963 with
    | [] -> failwith "set on empty option stack"
    | []::uu____997 -> failwith "set on empty current option stack"
    | (uu____1004::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
let (snapshot : unit -> (Prims.int, unit) FStar_Pervasives_Native.tuple2) =
  fun uu____1052 -> FStar_Common.snapshot push fstar_options ()
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth -> FStar_Common.rollback pop fstar_options depth
let (set_option : Prims.string -> option_val -> unit) =
  fun k ->
    fun v1 -> let uu____1076 = peek () in FStar_Util.smap_add uu____1076 k v1
let (set_option' :
  (Prims.string, option_val) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____1087 -> match uu____1087 with | (k, v1) -> set_option k v1
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref []
let (add_light_off_file : Prims.string -> unit) =
  fun filename ->
    let uu____1116 =
      let uu____1119 = FStar_ST.op_Bang light_off_files in filename ::
        uu____1119 in
    FStar_ST.op_Colon_Equals light_off_files uu____1116
let (defaults :
  (Prims.string, option_val) FStar_Pervasives_Native.tuple2 Prims.list) =
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
  fun uu____1586 ->
    let o = peek () in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
let (clear : unit -> unit) =
  fun uu____1603 ->
    let o = FStar_Util.smap_create (Prims.parse_int "50") in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
let (_run : unit) = clear ()
let (get_option : Prims.string -> option_val) =
  fun s ->
    let uu____1668 =
      let uu____1671 = peek () in FStar_Util.smap_try_find uu____1671 s in
    match uu____1668 with
    | FStar_Pervasives_Native.None ->
        failwith
          (Prims.strcat "Impossible: option " (Prims.strcat s " not found"))
    | FStar_Pervasives_Native.Some s1 -> s1
let lookup_opt :
  'Auu____1681 . Prims.string -> (option_val -> 'Auu____1681) -> 'Auu____1681
  = fun s -> fun c -> let uu____1697 = get_option s in c uu____1697
let (get_abort_on : unit -> Prims.int) =
  fun uu____1702 -> lookup_opt "abort_on" as_int
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____1707 -> lookup_opt "admit_smt_queries" as_bool
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____1714 -> lookup_opt "admit_except" (as_option as_string)
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____1721 -> lookup_opt "cache_checked_modules" as_bool
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1728 -> lookup_opt "cache_dir" (as_option as_string)
let (get_cache_off : unit -> Prims.bool) =
  fun uu____1735 -> lookup_opt "cache_off" as_bool
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1742 -> lookup_opt "codegen" (as_option as_string)
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____1751 -> lookup_opt "codegen-lib" (as_list as_string)
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____1760 -> lookup_opt "debug" (as_list as_string)
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____1769 -> lookup_opt "debug_level" as_comma_string_list
let (get_defensive : unit -> Prims.string) =
  fun uu____1776 -> lookup_opt "defensive" as_string
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1783 -> lookup_opt "dep" (as_option as_string)
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____1790 -> lookup_opt "detail_errors" as_bool
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____1795 -> lookup_opt "detail_hint_replay" as_bool
let (get_doc : unit -> Prims.bool) =
  fun uu____1800 -> lookup_opt "doc" as_bool
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____1807 -> lookup_opt "dump_module" (as_list as_string)
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____1814 -> lookup_opt "eager_subtyping" as_bool
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____1819 -> lookup_opt "expose_interfaces" as_bool
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____1828 -> lookup_opt "extract" (as_option (as_list as_string))
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____1841 -> lookup_opt "extract_module" (as_list as_string)
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____1850 -> lookup_opt "extract_namespace" (as_list as_string)
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____1857 -> lookup_opt "fs_typ_app" as_bool
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____1862 -> lookup_opt "hide_uvar_nums" as_bool
let (get_hint_info : unit -> Prims.bool) =
  fun uu____1867 -> lookup_opt "hint_info" as_bool
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____1874 -> lookup_opt "hint_file" (as_option as_string)
let (get_in : unit -> Prims.bool) = fun uu____1881 -> lookup_opt "in" as_bool
let (get_ide : unit -> Prims.bool) =
  fun uu____1886 -> lookup_opt "ide" as_bool
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____1893 -> lookup_opt "include" (as_list as_string)
let (get_indent : unit -> Prims.bool) =
  fun uu____1900 -> lookup_opt "indent" as_bool
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____1905 -> lookup_opt "initial_fuel" as_int
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____1910 -> lookup_opt "initial_ifuel" as_int
let (get_lax : unit -> Prims.bool) =
  fun uu____1915 -> lookup_opt "lax" as_bool
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____1922 -> lookup_opt "load" (as_list as_string)
let (get_log_queries : unit -> Prims.bool) =
  fun uu____1929 -> lookup_opt "log_queries" as_bool
let (get_log_types : unit -> Prims.bool) =
  fun uu____1934 -> lookup_opt "log_types" as_bool
let (get_max_fuel : unit -> Prims.int) =
  fun uu____1939 -> lookup_opt "max_fuel" as_int
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____1944 -> lookup_opt "max_ifuel" as_int
let (get_min_fuel : unit -> Prims.int) =
  fun uu____1949 -> lookup_opt "min_fuel" as_int
let (get_MLish : unit -> Prims.bool) =
  fun uu____1954 -> lookup_opt "MLish" as_bool
let (get_n_cores : unit -> Prims.int) =
  fun uu____1959 -> lookup_opt "n_cores" as_int
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____1964 -> lookup_opt "no_default_includes" as_bool
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____1971 -> lookup_opt "no_extract" (as_list as_string)
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____1978 -> lookup_opt "no_location_info" as_bool
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____1983 -> lookup_opt "no_plugins" as_bool
let (get_no_smt : unit -> Prims.bool) =
  fun uu____1988 -> lookup_opt "no_smt" as_bool
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____1993 -> lookup_opt "normalize_pure_terms_for_extraction" as_bool
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2000 -> lookup_opt "odir" (as_option as_string)
let (get_ugly : unit -> Prims.bool) =
  fun uu____2007 -> lookup_opt "ugly" as_bool
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2014 -> lookup_opt "prims" (as_option as_string)
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____2021 -> lookup_opt "print_bound_var_types" as_bool
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____2026 -> lookup_opt "print_effect_args" as_bool
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____2031 -> lookup_opt "print_full_names" as_bool
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____2036 -> lookup_opt "print_implicits" as_bool
let (get_print_universes : unit -> Prims.bool) =
  fun uu____2041 -> lookup_opt "print_universes" as_bool
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____2046 -> lookup_opt "print_z3_statistics" as_bool
let (get_prn : unit -> Prims.bool) =
  fun uu____2051 -> lookup_opt "prn" as_bool
let (get_query_stats : unit -> Prims.bool) =
  fun uu____2056 -> lookup_opt "query_stats" as_bool
let (get_record_hints : unit -> Prims.bool) =
  fun uu____2061 -> lookup_opt "record_hints" as_bool
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2068 -> lookup_opt "reuse_hint_for" (as_option as_string)
let (get_silent : unit -> Prims.bool) =
  fun uu____2075 -> lookup_opt "silent" as_bool
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2082 -> lookup_opt "smt" (as_option as_string)
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____2089 -> lookup_opt "smtencoding.elim_box" as_bool
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____2094 -> lookup_opt "smtencoding.nl_arith_repr" as_string
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____2099 -> lookup_opt "smtencoding.l_arith_repr" as_string
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____2104 -> lookup_opt "tactic_raw_binders" as_bool
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____2109 -> lookup_opt "tactics_failhard" as_bool
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____2114 -> lookup_opt "tactics_info" as_bool
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____2119 -> lookup_opt "tactic_trace" as_bool
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____2124 -> lookup_opt "tactic_trace_d" as_int
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____2129 -> lookup_opt "__tactics_nbe" as_bool
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____2134 -> lookup_opt "tcnorm" as_bool
let (get_timing : unit -> Prims.bool) =
  fun uu____2139 -> lookup_opt "timing" as_bool
let (get_trace_error : unit -> Prims.bool) =
  fun uu____2144 -> lookup_opt "trace_error" as_bool
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____2149 -> lookup_opt "unthrottle_inductives" as_bool
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____2154 -> lookup_opt "unsafe_tactic_exec" as_bool
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____2159 -> lookup_opt "use_eq_at_higher_order" as_bool
let (get_use_hints : unit -> Prims.bool) =
  fun uu____2164 -> lookup_opt "use_hints" as_bool
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____2169 -> lookup_opt "use_hint_hashes" as_bool
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2176 -> lookup_opt "use_native_tactics" (as_option as_string)
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____2183 ->
    let uu____2184 = lookup_opt "no_tactics" as_bool in
    Prims.op_Negation uu____2184
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2193 ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2206 ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____2215 -> lookup_opt "verify_module" (as_list as_string)
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____2224 -> lookup_opt "__temp_no_proj" (as_list as_string)
let (get_version : unit -> Prims.bool) =
  fun uu____2231 -> lookup_opt "version" as_bool
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____2236 -> lookup_opt "warn_default_effects" as_bool
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____2243 -> lookup_opt "z3cliopt" (as_list as_string)
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____2250 -> lookup_opt "z3refresh" as_bool
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____2255 -> lookup_opt "z3rlimit" as_int
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____2260 -> lookup_opt "z3rlimit_factor" as_int
let (get_z3seed : unit -> Prims.int) =
  fun uu____2265 -> lookup_opt "z3seed" as_int
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____2270 -> lookup_opt "use_two_phase_tc" as_bool
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____2275 -> lookup_opt "__no_positivity" as_bool
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____2280 -> lookup_opt "__ml_no_eta_expand_coertions" as_bool
let (get_warn_error : unit -> Prims.string) =
  fun uu____2285 -> lookup_opt "warn_error" as_string
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____2290 -> lookup_opt "use_extracted_interfaces" as_bool
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___82_2295 ->
    match uu___82_2295 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1 ->
    fun l2 ->
      match l1 with
      | Other uu____2307 -> l1 = l2
      | Low -> l1 = l2
      | Medium -> (l2 = Low) || (l2 = Medium)
      | High -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2 ->
    let uu____2313 = get_debug_level () in
    FStar_All.pipe_right uu____2313
      (FStar_Util.for_some (fun l1 -> one_debug_level_geq (dlevel l1) l2))
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"]
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref ""
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref ""
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref ""
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref ""
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref ""
let (display_version : unit -> unit) =
  fun uu____2446 ->
    let uu____2447 =
      let uu____2448 = FStar_ST.op_Bang _version in
      let uu____2468 = FStar_ST.op_Bang _platform in
      let uu____2488 = FStar_ST.op_Bang _compiler in
      let uu____2508 = FStar_ST.op_Bang _date in
      let uu____2528 = FStar_ST.op_Bang _commit in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____2448
        uu____2468 uu____2488 uu____2508 uu____2528 in
    FStar_Util.print_string uu____2447
let display_usage_aux :
  'Auu____2554 'Auu____2555 .
    ('Auu____2554, Prims.string, 'Auu____2555 FStar_Getopt.opt_variant,
      Prims.string) FStar_Pervasives_Native.tuple4 Prims.list -> unit
  =
  fun specs ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____2603 ->
         match uu____2603 with
         | (uu____2614, flag, p, doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____2626 =
                      let uu____2627 = FStar_Util.colorize_bold flag in
                      FStar_Util.format1 "  --%s\n" uu____2627 in
                    FStar_Util.print_string uu____2626
                  else
                    (let uu____2629 =
                       let uu____2630 = FStar_Util.colorize_bold flag in
                       FStar_Util.format2 "  --%s  %s\n" uu____2630 doc in
                     FStar_Util.print_string uu____2629)
              | FStar_Getopt.OneArg (uu____2631, argname) ->
                  if doc = ""
                  then
                    let uu____2639 =
                      let uu____2640 = FStar_Util.colorize_bold flag in
                      let uu____2641 = FStar_Util.colorize_bold argname in
                      FStar_Util.format2 "  --%s %s\n" uu____2640 uu____2641 in
                    FStar_Util.print_string uu____2639
                  else
                    (let uu____2643 =
                       let uu____2644 = FStar_Util.colorize_bold flag in
                       let uu____2645 = FStar_Util.colorize_bold argname in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____2644
                         uu____2645 doc in
                     FStar_Util.print_string uu____2643))) specs
let (mk_spec :
  (FStar_BaseTypes.char, Prims.string, option_val FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 -> FStar_Getopt.opt)
  =
  fun o ->
    let uu____2673 = o in
    match uu____2673 with
    | (ns, name, arg, desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____2709 =
                let uu____2710 = f () in set_option name uu____2710 in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f, d) ->
              let g x = let uu____2725 = f x in set_option name uu____2725 in
              FStar_Getopt.OneArg (g, d) in
        (ns, name, arg1, desc)
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name ->
    fun value ->
      let prev_values =
        let uu____2745 = lookup_opt name (as_option as_list') in
        FStar_Util.dflt [] uu____2745 in
      mk_list (value :: prev_values)
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name ->
    fun value ->
      let uu____2768 =
        let uu____2771 = lookup_opt name as_list' in
        FStar_List.append uu____2771 [value] in
      mk_list uu____2768
let accumulate_string :
  'Auu____2784 .
    Prims.string -> ('Auu____2784 -> Prims.string) -> 'Auu____2784 -> unit
  =
  fun name ->
    fun post_processor ->
      fun value ->
        let uu____2805 =
          let uu____2806 =
            let uu____2807 = post_processor value in mk_string uu____2807 in
          accumulated_option name uu____2806 in
        set_option name uu____2805
let (add_extract_module : Prims.string -> unit) =
  fun s -> accumulate_string "extract_module" FStar_String.lowercase s
let (add_extract_namespace : Prims.string -> unit) =
  fun s -> accumulate_string "extract_namespace" FStar_String.lowercase s
let (add_verify_module : Prims.string -> unit) =
  fun s -> accumulate_string "verify_module" FStar_String.lowercase s
type opt_type =
  | Const of option_val 
  | IntStr of Prims.string 
  | BoolStr 
  | PathStr of Prims.string 
  | SimpleStr of Prims.string 
  | EnumStr of Prims.string Prims.list 
  | OpenEnumStr of (Prims.string Prims.list, Prims.string)
  FStar_Pervasives_Native.tuple2 
  | PostProcessed of (option_val -> option_val, opt_type)
  FStar_Pervasives_Native.tuple2 
  | Accumulated of opt_type 
  | ReverseAccumulated of opt_type 
  | WithSideEffect of (unit -> unit, opt_type) FStar_Pervasives_Native.tuple2 
let (uu___is_Const : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | Const _0 -> true | uu____2903 -> false
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee -> match projectee with | Const _0 -> _0
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | IntStr _0 -> true | uu____2917 -> false
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee -> match projectee with | IntStr _0 -> _0
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | BoolStr -> true | uu____2930 -> false
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | PathStr _0 -> true | uu____2937 -> false
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee -> match projectee with | PathStr _0 -> _0
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | SimpleStr _0 -> true | uu____2951 -> false
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee -> match projectee with | SimpleStr _0 -> _0
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | EnumStr _0 -> true | uu____2967 -> false
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee -> match projectee with | EnumStr _0 -> _0
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | OpenEnumStr _0 -> true | uu____2993 -> false
let (__proj__OpenEnumStr__item___0 :
  opt_type ->
    (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | OpenEnumStr _0 -> _0
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | PostProcessed _0 -> true | uu____3032 -> false
let (__proj__PostProcessed__item___0 :
  opt_type ->
    (option_val -> option_val, opt_type) FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | PostProcessed _0 -> _0
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | Accumulated _0 -> true | uu____3067 -> false
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee -> match projectee with | Accumulated _0 -> _0
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____3081 -> false
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee -> match projectee with | ReverseAccumulated _0 -> _0
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | WithSideEffect _0 -> true | uu____3102 -> false
let (__proj__WithSideEffect__item___0 :
  opt_type -> (unit -> unit, opt_type) FStar_Pervasives_Native.tuple2) =
  fun projectee -> match projectee with | WithSideEffect _0 -> _0
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | InvalidArgument uu____3140 -> true
    | uu____3141 -> false
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | InvalidArgument uu____3148 -> uu____3148
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name ->
    fun typ ->
      fun str_val ->
        try
          (fun uu___87_3166 ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____3168 ->
                      let uu____3169 = FStar_Util.safe_int_of_string str_val in
                      (match uu____3169 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr ->
                      let uu____3173 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name) in
                      mk_bool uu____3173
                  | PathStr uu____3176 -> mk_path str_val
                  | SimpleStr uu____3177 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____3182 -> mk_string str_val
                  | PostProcessed (pp, elem_spec) ->
                      let uu____3197 =
                        parse_opt_val opt_name elem_spec str_val in
                      pp uu____3197
                  | Accumulated elem_spec ->
                      let v1 = parse_opt_val opt_name elem_spec str_val in
                      accumulated_option opt_name v1
                  | ReverseAccumulated elem_spec ->
                      let v1 = parse_opt_val opt_name elem_spec str_val in
                      reverse_accumulated_option opt_name v1
                  | WithSideEffect (side_effect, elem_spec) ->
                      (side_effect ();
                       parse_opt_val opt_name elem_spec str_val))) ()
        with
        | InvalidArgument opt_name1 ->
            let uu____3216 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1 in
            failwith uu____3216
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ ->
    let desc_of_enum cases =
      FStar_Pervasives_Native.Some
        (Prims.strcat "[" (Prims.strcat (FStar_String.concat "|" cases) "]")) in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs, desc) ->
        desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____3253, elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____3263, elem_spec) -> desc_of_opt_type elem_spec
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name ->
    fun typ ->
      let parser = parse_opt_val opt_name typ in
      let uu____3290 = desc_of_opt_type typ in
      match uu____3290 with
      | FStar_Pervasives_Native.None ->
          FStar_Getopt.ZeroArgs ((fun uu____3296 -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
let (pp_validate_dir : option_val -> option_val) =
  fun p -> let pp = as_string p in FStar_Util.mkdir false pp; p
let (pp_lowercase : option_val -> option_val) =
  fun s ->
    let uu____3313 =
      let uu____3314 = as_string s in FStar_String.lowercase uu____3314 in
    mk_string uu____3313
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0")
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char, Prims.string, opt_type, Prims.string)
      FStar_Pervasives_Native.tuple4 Prims.list)
  =
  fun uu____3362 ->
    let uu____3374 =
      let uu____3386 =
        let uu____3398 =
          let uu____3410 =
            let uu____3420 =
              let uu____3421 = mk_bool true in Const uu____3421 in
            (FStar_Getopt.noshort, "cache_checked_modules", uu____3420,
              "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying") in
          let uu____3423 =
            let uu____3435 =
              let uu____3447 =
                let uu____3457 =
                  let uu____3458 = mk_bool true in Const uu____3458 in
                (FStar_Getopt.noshort, "cache_off", uu____3457,
                  "Do not read or write any .checked files") in
              let uu____3460 =
                let uu____3472 =
                  let uu____3484 =
                    let uu____3496 =
                      let uu____3508 =
                        let uu____3520 =
                          let uu____3532 =
                            let uu____3544 =
                              let uu____3554 =
                                let uu____3555 = mk_bool true in
                                Const uu____3555 in
                              (FStar_Getopt.noshort, "detail_errors",
                                uu____3554,
                                "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1") in
                            let uu____3557 =
                              let uu____3569 =
                                let uu____3579 =
                                  let uu____3580 = mk_bool true in
                                  Const uu____3580 in
                                (FStar_Getopt.noshort, "detail_hint_replay",
                                  uu____3579,
                                  "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1") in
                              let uu____3582 =
                                let uu____3594 =
                                  let uu____3604 =
                                    let uu____3605 = mk_bool true in
                                    Const uu____3605 in
                                  (FStar_Getopt.noshort, "doc", uu____3604,
                                    "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.") in
                                let uu____3607 =
                                  let uu____3619 =
                                    let uu____3631 =
                                      let uu____3641 =
                                        let uu____3642 = mk_bool true in
                                        Const uu____3642 in
                                      (FStar_Getopt.noshort,
                                        "eager_inference", uu____3641,
                                        "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality") in
                                    let uu____3644 =
                                      let uu____3656 =
                                        let uu____3666 =
                                          let uu____3667 = mk_bool true in
                                          Const uu____3667 in
                                        (FStar_Getopt.noshort,
                                          "eager_subtyping", uu____3666,
                                          "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)") in
                                      let uu____3669 =
                                        let uu____3681 =
                                          let uu____3693 =
                                            let uu____3705 =
                                              let uu____3717 =
                                                let uu____3727 =
                                                  let uu____3728 =
                                                    mk_bool true in
                                                  Const uu____3728 in
                                                (FStar_Getopt.noshort,
                                                  "expose_interfaces",
                                                  uu____3727,
                                                  "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)") in
                                              let uu____3730 =
                                                let uu____3742 =
                                                  let uu____3752 =
                                                    let uu____3753 =
                                                      mk_bool true in
                                                    Const uu____3753 in
                                                  (FStar_Getopt.noshort,
                                                    "hide_uvar_nums",
                                                    uu____3752,
                                                    "Don't print unification variable numbers") in
                                                let uu____3755 =
                                                  let uu____3767 =
                                                    let uu____3779 =
                                                      let uu____3789 =
                                                        let uu____3790 =
                                                          mk_bool true in
                                                        Const uu____3790 in
                                                      (FStar_Getopt.noshort,
                                                        "hint_info",
                                                        uu____3789,
                                                        "Print information regarding hints (deprecated; use --query_stats instead)") in
                                                    let uu____3792 =
                                                      let uu____3804 =
                                                        let uu____3814 =
                                                          let uu____3815 =
                                                            mk_bool true in
                                                          Const uu____3815 in
                                                        (FStar_Getopt.noshort,
                                                          "in", uu____3814,
                                                          "Legacy interactive mode; reads input from stdin") in
                                                      let uu____3817 =
                                                        let uu____3829 =
                                                          let uu____3839 =
                                                            let uu____3840 =
                                                              mk_bool true in
                                                            Const uu____3840 in
                                                          (FStar_Getopt.noshort,
                                                            "ide",
                                                            uu____3839,
                                                            "JSON-based interactive mode for IDEs") in
                                                        let uu____3842 =
                                                          let uu____3854 =
                                                            let uu____3866 =
                                                              let uu____3876
                                                                =
                                                                let uu____3877
                                                                  =
                                                                  mk_bool
                                                                    true in
                                                                Const
                                                                  uu____3877 in
                                                              (FStar_Getopt.noshort,
                                                                "indent",
                                                                uu____3876,
                                                                "Parses and outputs the files on the command line") in
                                                            let uu____3879 =
                                                              let uu____3891
                                                                =
                                                                let uu____3903
                                                                  =
                                                                  let uu____3915
                                                                    =
                                                                    let uu____3925
                                                                    =
                                                                    let uu____3926
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3926 in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____3925,
                                                                    "Run the lax-type checker only (admit all verification conditions)") in
                                                                  let uu____3928
                                                                    =
                                                                    let uu____3940
                                                                    =
                                                                    let uu____3952
                                                                    =
                                                                    let uu____3962
                                                                    =
                                                                    let uu____3963
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3963 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____3962,
                                                                    "Print types computed for data/val/let-bindings") in
                                                                    let uu____3965
                                                                    =
                                                                    let uu____3977
                                                                    =
                                                                    let uu____3987
                                                                    =
                                                                    let uu____3988
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____3988 in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____3987,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go") in
                                                                    let uu____3990
                                                                    =
                                                                    let uu____4002
                                                                    =
                                                                    let uu____4014
                                                                    =
                                                                    let uu____4026
                                                                    =
                                                                    let uu____4038
                                                                    =
                                                                    let uu____4048
                                                                    =
                                                                    let uu____4049
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4049 in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____4048,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)") in
                                                                    let uu____4051
                                                                    =
                                                                    let uu____4063
                                                                    =
                                                                    let uu____4075
                                                                    =
                                                                    let uu____4085
                                                                    =
                                                                    let uu____4086
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4086 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____4085,
                                                                    "Ignore the default module search paths") in
                                                                    let uu____4088
                                                                    =
                                                                    let uu____4100
                                                                    =
                                                                    let uu____4112
                                                                    =
                                                                    let uu____4122
                                                                    =
                                                                    let uu____4123
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4123 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____4122,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)") in
                                                                    let uu____4125
                                                                    =
                                                                    let uu____4137
                                                                    =
                                                                    let uu____4147
                                                                    =
                                                                    let uu____4148
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4148 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____4147,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead") in
                                                                    let uu____4150
                                                                    =
                                                                    let uu____4162
                                                                    =
                                                                    let uu____4172
                                                                    =
                                                                    let uu____4173
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4173 in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____4172,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.") in
                                                                    let uu____4175
                                                                    =
                                                                    let uu____4187
                                                                    =
                                                                    let uu____4199
                                                                    =
                                                                    let uu____4211
                                                                    =
                                                                    let uu____4221
                                                                    =
                                                                    let uu____4222
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4222 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____4221,
                                                                    "Print the types of bound variables") in
                                                                    let uu____4224
                                                                    =
                                                                    let uu____4236
                                                                    =
                                                                    let uu____4246
                                                                    =
                                                                    let uu____4247
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4247 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____4246,
                                                                    "Print inferred predicate transformers for all computation types") in
                                                                    let uu____4249
                                                                    =
                                                                    let uu____4261
                                                                    =
                                                                    let uu____4271
                                                                    =
                                                                    let uu____4272
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4272 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____4271,
                                                                    "Print full names of variables") in
                                                                    let uu____4274
                                                                    =
                                                                    let uu____4286
                                                                    =
                                                                    let uu____4296
                                                                    =
                                                                    let uu____4297
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4297 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____4296,
                                                                    "Print implicit arguments") in
                                                                    let uu____4299
                                                                    =
                                                                    let uu____4311
                                                                    =
                                                                    let uu____4321
                                                                    =
                                                                    let uu____4322
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4322 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____4321,
                                                                    "Print universes") in
                                                                    let uu____4324
                                                                    =
                                                                    let uu____4336
                                                                    =
                                                                    let uu____4346
                                                                    =
                                                                    let uu____4347
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4347 in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____4346,
                                                                    "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)") in
                                                                    let uu____4349
                                                                    =
                                                                    let uu____4361
                                                                    =
                                                                    let uu____4371
                                                                    =
                                                                    let uu____4372
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4372 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____4371,
                                                                    "Print full names (deprecated; use --print_full_names instead)") in
                                                                    let uu____4374
                                                                    =
                                                                    let uu____4386
                                                                    =
                                                                    let uu____4396
                                                                    =
                                                                    let uu____4397
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4397 in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____4396,
                                                                    "Print SMT query statistics") in
                                                                    let uu____4399
                                                                    =
                                                                    let uu____4411
                                                                    =
                                                                    let uu____4421
                                                                    =
                                                                    let uu____4422
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4422 in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____4421,
                                                                    "Record a database of hints for efficient proof replay") in
                                                                    let uu____4424
                                                                    =
                                                                    let uu____4436
                                                                    =
                                                                    let uu____4448
                                                                    =
                                                                    let uu____4458
                                                                    =
                                                                    let uu____4459
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4459 in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____4458,
                                                                    " ") in
                                                                    let uu____4461
                                                                    =
                                                                    let uu____4473
                                                                    =
                                                                    let uu____4485
                                                                    =
                                                                    let uu____4497
                                                                    =
                                                                    let uu____4509
                                                                    =
                                                                    let uu____4521
                                                                    =
                                                                    let uu____4531
                                                                    =
                                                                    let uu____4532
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4532 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____4531,
                                                                    "Do not use the lexical scope of tactics to improve binder names") in
                                                                    let uu____4534
                                                                    =
                                                                    let uu____4546
                                                                    =
                                                                    let uu____4556
                                                                    =
                                                                    let uu____4557
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4557 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____4556,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs") in
                                                                    let uu____4559
                                                                    =
                                                                    let uu____4571
                                                                    =
                                                                    let uu____4581
                                                                    =
                                                                    let uu____4582
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4582 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____4581,
                                                                    "Print some rough information on tactics, such as the time they take to run") in
                                                                    let uu____4584
                                                                    =
                                                                    let uu____4596
                                                                    =
                                                                    let uu____4606
                                                                    =
                                                                    let uu____4607
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4607 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____4606,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)") in
                                                                    let uu____4609
                                                                    =
                                                                    let uu____4621
                                                                    =
                                                                    let uu____4633
                                                                    =
                                                                    let uu____4643
                                                                    =
                                                                    let uu____4644
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4644 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____4643,
                                                                    "Use NBE to evaluate metaprograms (experimental)") in
                                                                    let uu____4646
                                                                    =
                                                                    let uu____4658
                                                                    =
                                                                    let uu____4670
                                                                    =
                                                                    let uu____4680
                                                                    =
                                                                    let uu____4681
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4681 in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____4680,
                                                                    "Print the time it takes to verify each top-level definition") in
                                                                    let uu____4683
                                                                    =
                                                                    let uu____4695
                                                                    =
                                                                    let uu____4705
                                                                    =
                                                                    let uu____4706
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4706 in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____4705,
                                                                    "Don't print an error message; show an exception trace instead") in
                                                                    let uu____4708
                                                                    =
                                                                    let uu____4720
                                                                    =
                                                                    let uu____4730
                                                                    =
                                                                    let uu____4731
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4731 in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____4730,
                                                                    "Emit output formatted for debugging") in
                                                                    let uu____4733
                                                                    =
                                                                    let uu____4745
                                                                    =
                                                                    let uu____4755
                                                                    =
                                                                    let uu____4756
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4756 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____4755,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)") in
                                                                    let uu____4758
                                                                    =
                                                                    let uu____4770
                                                                    =
                                                                    let uu____4780
                                                                    =
                                                                    let uu____4781
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4781 in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____4780,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.") in
                                                                    let uu____4783
                                                                    =
                                                                    let uu____4795
                                                                    =
                                                                    let uu____4805
                                                                    =
                                                                    let uu____4806
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4806 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____4805,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)") in
                                                                    let uu____4808
                                                                    =
                                                                    let uu____4820
                                                                    =
                                                                    let uu____4830
                                                                    =
                                                                    let uu____4831
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4831 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____4830,
                                                                    "Use a previously recorded hints database for proof replay") in
                                                                    let uu____4833
                                                                    =
                                                                    let uu____4845
                                                                    =
                                                                    let uu____4855
                                                                    =
                                                                    let uu____4856
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4856 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____4855,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database") in
                                                                    let uu____4858
                                                                    =
                                                                    let uu____4870
                                                                    =
                                                                    let uu____4882
                                                                    =
                                                                    let uu____4892
                                                                    =
                                                                    let uu____4893
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4893 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____4892,
                                                                    "Do not run plugins natively and interpret them as usual instead") in
                                                                    let uu____4895
                                                                    =
                                                                    let uu____4907
                                                                    =
                                                                    let uu____4917
                                                                    =
                                                                    let uu____4918
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4918 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____4917,
                                                                    "Do not run the tactic engine before discharging a VC") in
                                                                    let uu____4920
                                                                    =
                                                                    let uu____4932
                                                                    =
                                                                    let uu____4944
                                                                    =
                                                                    let uu____4956
                                                                    =
                                                                    let uu____4968
                                                                    =
                                                                    let uu____4978
                                                                    =
                                                                    let uu____4979
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____4979 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____4978,
                                                                    "Don't use this option yet") in
                                                                    let uu____4981
                                                                    =
                                                                    let uu____4993
                                                                    =
                                                                    let uu____5003
                                                                    =
                                                                    let uu____5004
                                                                    =
                                                                    let uu____5012
                                                                    =
                                                                    let uu____5013
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____5013 in
                                                                    ((fun
                                                                    uu____5019
                                                                    ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____5012) in
                                                                    WithSideEffect
                                                                    uu____5004 in
                                                                    (118,
                                                                    "version",
                                                                    uu____5003,
                                                                    "Display version number") in
                                                                    let uu____5023
                                                                    =
                                                                    let uu____5035
                                                                    =
                                                                    let uu____5045
                                                                    =
                                                                    let uu____5046
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____5046 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____5045,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)") in
                                                                    let uu____5048
                                                                    =
                                                                    let uu____5060
                                                                    =
                                                                    let uu____5072
                                                                    =
                                                                    let uu____5082
                                                                    =
                                                                    let uu____5083
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____5083 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____5082,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness") in
                                                                    let uu____5085
                                                                    =
                                                                    let uu____5097
                                                                    =
                                                                    let uu____5109
                                                                    =
                                                                    let uu____5121
                                                                    =
                                                                    let uu____5133
                                                                    =
                                                                    let uu____5145
                                                                    =
                                                                    let uu____5155
                                                                    =
                                                                    let uu____5156
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____5156 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____5155,
                                                                    "Don't check positivity of inductive types") in
                                                                    let uu____5158
                                                                    =
                                                                    let uu____5170
                                                                    =
                                                                    let uu____5180
                                                                    =
                                                                    let uu____5181
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____5181 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____5180,
                                                                    "Do not eta-expand coertions in generated OCaml") in
                                                                    let uu____5183
                                                                    =
                                                                    let uu____5195
                                                                    =
                                                                    let uu____5207
                                                                    =
                                                                    let uu____5219
                                                                    =
                                                                    let uu____5229
                                                                    =
                                                                    let uu____5230
                                                                    =
                                                                    let uu____5238
                                                                    =
                                                                    let uu____5239
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____5239 in
                                                                    ((fun
                                                                    uu____5244
                                                                    ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____5238) in
                                                                    WithSideEffect
                                                                    uu____5230 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____5229,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms") in
                                                                    let uu____5265
                                                                    =
                                                                    let uu____5277
                                                                    =
                                                                    let uu____5287
                                                                    =
                                                                    let uu____5288
                                                                    =
                                                                    let uu____5296
                                                                    =
                                                                    let uu____5297
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____5297 in
                                                                    ((fun
                                                                    uu____5302
                                                                    ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____5296) in
                                                                    WithSideEffect
                                                                    uu____5288 in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____5287,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking") in
                                                                    let uu____5323
                                                                    =
                                                                    let uu____5335
                                                                    =
                                                                    let uu____5345
                                                                    =
                                                                    let uu____5346
                                                                    =
                                                                    let uu____5354
                                                                    =
                                                                    let uu____5355
                                                                    =
                                                                    mk_bool
                                                                    true in
                                                                    Const
                                                                    uu____5355 in
                                                                    ((fun
                                                                    uu____5361
                                                                    ->
                                                                    (
                                                                    let uu____5363
                                                                    =
                                                                    specs () in
                                                                    display_usage_aux
                                                                    uu____5363);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____5354) in
                                                                    WithSideEffect
                                                                    uu____5346 in
                                                                    (104,
                                                                    "help",
                                                                    uu____5345,
                                                                    "Display this information") in
                                                                    [uu____5335] in
                                                                    uu____5277
                                                                    ::
                                                                    uu____5323 in
                                                                    uu____5219
                                                                    ::
                                                                    uu____5265 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____5207 in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (SimpleStr
                                                                    ""),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____5195 in
                                                                    uu____5170
                                                                    ::
                                                                    uu____5183 in
                                                                    uu____5145
                                                                    ::
                                                                    uu____5158 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____5133 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____5121 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____5109 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____5097 in
                                                                    uu____5072
                                                                    ::
                                                                    uu____5085 in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____5060 in
                                                                    uu____5035
                                                                    ::
                                                                    uu____5048 in
                                                                    uu____4993
                                                                    ::
                                                                    uu____5023 in
                                                                    uu____4968
                                                                    ::
                                                                    uu____4981 in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____4956 in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____4944 in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____4932 in
                                                                    uu____4907
                                                                    ::
                                                                    uu____4920 in
                                                                    uu____4882
                                                                    ::
                                                                    uu____4895 in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____4870 in
                                                                    uu____4845
                                                                    ::
                                                                    uu____4858 in
                                                                    uu____4820
                                                                    ::
                                                                    uu____4833 in
                                                                    uu____4795
                                                                    ::
                                                                    uu____4808 in
                                                                    uu____4770
                                                                    ::
                                                                    uu____4783 in
                                                                    uu____4745
                                                                    ::
                                                                    uu____4758 in
                                                                    uu____4720
                                                                    ::
                                                                    uu____4733 in
                                                                    uu____4695
                                                                    ::
                                                                    uu____4708 in
                                                                    uu____4670
                                                                    ::
                                                                    uu____4683 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____4658 in
                                                                    uu____4633
                                                                    ::
                                                                    uu____4646 in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____4621 in
                                                                    uu____4596
                                                                    ::
                                                                    uu____4609 in
                                                                    uu____4571
                                                                    ::
                                                                    uu____4584 in
                                                                    uu____4546
                                                                    ::
                                                                    uu____4559 in
                                                                    uu____4521
                                                                    ::
                                                                    uu____4534 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4509 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____4497 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____4485 in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____4473 in
                                                                    uu____4448
                                                                    ::
                                                                    uu____4461 in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____4436 in
                                                                    uu____4411
                                                                    ::
                                                                    uu____4424 in
                                                                    uu____4386
                                                                    ::
                                                                    uu____4399 in
                                                                    uu____4361
                                                                    ::
                                                                    uu____4374 in
                                                                    uu____4336
                                                                    ::
                                                                    uu____4349 in
                                                                    uu____4311
                                                                    ::
                                                                    uu____4324 in
                                                                    uu____4286
                                                                    ::
                                                                    uu____4299 in
                                                                    uu____4261
                                                                    ::
                                                                    uu____4274 in
                                                                    uu____4236
                                                                    ::
                                                                    uu____4249 in
                                                                    uu____4211
                                                                    ::
                                                                    uu____4224 in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____4199 in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____4187 in
                                                                    uu____4162
                                                                    ::
                                                                    uu____4175 in
                                                                    uu____4137
                                                                    ::
                                                                    uu____4150 in
                                                                    uu____4112
                                                                    ::
                                                                    uu____4125 in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____4100 in
                                                                    uu____4075
                                                                    ::
                                                                    uu____4088 in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____4063 in
                                                                    uu____4038
                                                                    ::
                                                                    uu____4051 in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____4026 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____4014 in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____4002 in
                                                                    uu____3977
                                                                    ::
                                                                    uu____3990 in
                                                                    uu____3952
                                                                    ::
                                                                    uu____3965 in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____3940 in
                                                                  uu____3915
                                                                    ::
                                                                    uu____3928 in
                                                                (FStar_Getopt.noshort,
                                                                  "initial_ifuel",
                                                                  (IntStr
                                                                    "non-negative integer"),
                                                                  "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                  ::
                                                                  uu____3903 in
                                                              (FStar_Getopt.noshort,
                                                                "initial_fuel",
                                                                (IntStr
                                                                   "non-negative integer"),
                                                                "Number of unrolling of recursive functions to try initially (default 2)")
                                                                :: uu____3891 in
                                                            uu____3866 ::
                                                              uu____3879 in
                                                          (FStar_Getopt.noshort,
                                                            "include",
                                                            (ReverseAccumulated
                                                               (PathStr
                                                                  "path")),
                                                            "A directory in which to search for files included on the command line")
                                                            :: uu____3854 in
                                                        uu____3829 ::
                                                          uu____3842 in
                                                      uu____3804 ::
                                                        uu____3817 in
                                                    uu____3779 :: uu____3792 in
                                                  (FStar_Getopt.noshort,
                                                    "hint_file",
                                                    (PathStr "path"),
                                                    "Read/write hints to <path> (instead of module-specific hints files)")
                                                    :: uu____3767 in
                                                uu____3742 :: uu____3755 in
                                              uu____3717 :: uu____3730 in
                                            (FStar_Getopt.noshort,
                                              "extract_namespace",
                                              (Accumulated
                                                 (PostProcessed
                                                    (pp_lowercase,
                                                      (SimpleStr
                                                         "namespace name")))),
                                              "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                              :: uu____3705 in
                                          (FStar_Getopt.noshort,
                                            "extract_module",
                                            (Accumulated
                                               (PostProcessed
                                                  (pp_lowercase,
                                                    (SimpleStr "module_name")))),
                                            "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                            :: uu____3693 in
                                        (FStar_Getopt.noshort, "extract",
                                          (Accumulated
                                             (SimpleStr
                                                "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                          "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                          :: uu____3681 in
                                      uu____3656 :: uu____3669 in
                                    uu____3631 :: uu____3644 in
                                  (FStar_Getopt.noshort, "dump_module",
                                    (Accumulated (SimpleStr "module_name")),
                                    "") :: uu____3619 in
                                uu____3594 :: uu____3607 in
                              uu____3569 :: uu____3582 in
                            uu____3544 :: uu____3557 in
                          (FStar_Getopt.noshort, "dep",
                            (EnumStr ["make"; "graph"; "full"; "raw"]),
                            "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                            :: uu____3532 in
                        (FStar_Getopt.noshort, "defensive",
                          (EnumStr ["no"; "warn"; "fail"]),
                          "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                          :: uu____3520 in
                      (FStar_Getopt.noshort, "debug_level",
                        (Accumulated
                           (OpenEnumStr
                              (["Low"; "Medium"; "High"; "Extreme"], "..."))),
                        "Control the verbosity of debugging info") ::
                        uu____3508 in
                    (FStar_Getopt.noshort, "debug",
                      (Accumulated (SimpleStr "module_name")),
                      "Print lots of debugging information while checking module")
                      :: uu____3496 in
                  (FStar_Getopt.noshort, "codegen-lib",
                    (Accumulated (SimpleStr "namespace")),
                    "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                    :: uu____3484 in
                (FStar_Getopt.noshort, "codegen",
                  (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                  "Generate code for further compilation to executable code, or build a compiler plugin")
                  :: uu____3472 in
              uu____3447 :: uu____3460 in
            (FStar_Getopt.noshort, "cache_dir",
              (PostProcessed (pp_validate_dir, (PathStr "dir"))),
              "Read and write .checked and .checked.lax in directory <dir>")
              :: uu____3435 in
          uu____3410 :: uu____3423 in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____3398 in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____3386 in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___83_6344 ->
             match uu___83_6344 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____3374
and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____6367 ->
    let uu____6370 = specs_with_types () in
    FStar_List.map
      (fun uu____6397 ->
         match uu____6397 with
         | (short, long, typ, doc) ->
             let uu____6413 =
               let uu____6425 = arg_spec_of_opt_type long typ in
               (short, long, uu____6425, doc) in
             mk_spec uu____6413) uu____6370
let (settable : Prims.string -> Prims.bool) =
  fun uu___84_6435 ->
    match uu___84_6435 with
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
    | uu____6436 -> false
let (resettable : Prims.string -> Prims.bool) =
  fun s ->
    (((settable s) || (s = "z3seed")) || (s = "z3cliopt")) ||
      (s = "using_facts_from")
let (all_specs : FStar_Getopt.opt Prims.list) = specs ()
let (all_specs_with_types :
  (FStar_BaseTypes.char, Prims.string, opt_type, Prims.string)
    FStar_Pervasives_Native.tuple4 Prims.list)
  = specs_with_types ()
let (settable_specs :
  (FStar_BaseTypes.char, Prims.string, unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____6510 ->
          match uu____6510 with
          | (uu____6522, x, uu____6524, uu____6525) -> settable x))
let (resettable_specs :
  (FStar_BaseTypes.char, Prims.string, unit FStar_Getopt.opt_variant,
    Prims.string) FStar_Pervasives_Native.tuple4 Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____6587 ->
          match uu____6587 with
          | (uu____6599, x, uu____6601, uu____6602) -> resettable x))
let (display_usage : unit -> unit) =
  fun uu____6613 -> let uu____6614 = specs () in display_usage_aux uu____6614
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir ()
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | File_argument uu____6638 -> true
    | uu____6639 -> false
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | File_argument uu____6646 -> uu____6646
let (set_options : options -> Prims.string -> FStar_Getopt.parse_cmdline_res)
  =
  fun o ->
    fun s ->
      let specs1 =
        match o with
        | Set -> settable_specs
        | Reset -> resettable_specs
        | Restore -> all_specs in
      try
        (fun uu___89_6663 ->
           match () with
           | () ->
               if s = ""
               then FStar_Getopt.Success
               else
                 FStar_Getopt.parse_string specs1
                   (fun s1 -> FStar_Exn.raise (File_argument s1)) s) ()
      with
      | File_argument s1 ->
          let uu____6674 =
            FStar_Util.format1 "File %s is not a valid option" s1 in
          FStar_Getopt.Error uu____6674
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref []
let (parse_cmd_line :
  unit ->
    (FStar_Getopt.parse_cmdline_res, Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu____6702 ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i ->
           let uu____6707 =
             let uu____6710 = FStar_ST.op_Bang file_list_ in
             FStar_List.append uu____6710 [i] in
           FStar_ST.op_Colon_Equals file_list_ uu____6707) in
    let uu____6759 =
      let uu____6762 = FStar_ST.op_Bang file_list_ in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____6762 in
    (res, uu____6759)
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____6796 -> FStar_ST.op_Bang file_list_
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let r =
       let uu____6831 = specs () in
       FStar_Getopt.parse_cmdline uu____6831 (fun x -> ()) in
     (let uu____6837 =
        let uu____6842 =
          let uu____6843 = FStar_List.map mk_string old_verify_module in
          List uu____6843 in
        ("verify_module", uu____6842) in
      set_option' uu____6837);
     r)
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f ->
    let f1 = FStar_Util.basename f in
    let f2 =
      let uu____6853 =
        let uu____6854 =
          let uu____6855 =
            let uu____6856 = FStar_Util.get_file_extension f1 in
            FStar_String.length uu____6856 in
          (FStar_String.length f1) - uu____6855 in
        uu____6854 - (Prims.parse_int "1") in
      FStar_String.substring f1 (Prims.parse_int "0") uu____6853 in
    FStar_String.lowercase f2
let (should_verify : Prims.string -> Prims.bool) =
  fun m ->
    let uu____6862 = get_lax () in
    if uu____6862
    then false
    else
      (let l = get_verify_module () in
       FStar_List.contains (FStar_String.lowercase m) l)
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn ->
    let uu____6872 = module_name_of_file_name fn in should_verify uu____6872
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m ->
    let uu____6878 = get___temp_no_proj () in
    FStar_List.contains m uu____6878
let (should_print_message : Prims.string -> Prims.bool) =
  fun m ->
    let uu____6886 = should_verify m in
    if uu____6886 then m <> "Prims" else false
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____6894 ->
    let uu____6895 = get_no_default_includes () in
    if uu____6895
    then get_include ()
    else
      (let lib_paths =
         let uu____6902 = FStar_Util.expand_environment_variable "FSTAR_LIB" in
         match uu____6902 with
         | FStar_Pervasives_Native.None ->
             let fstar_home = Prims.strcat fstar_bin_directory "/.." in
             let defs = universe_include_path_base_dirs in
             let uu____6911 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x -> Prims.strcat fstar_home x)) in
             FStar_All.pipe_right uu____6911
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s] in
       let uu____6925 =
         let uu____6928 = get_include () in
         FStar_List.append uu____6928 ["."] in
       FStar_List.append lib_paths uu____6925)
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100") in
  fun filename ->
    let uu____6941 = FStar_Util.smap_try_find file_map filename in
    match uu____6941 with
    | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
    | FStar_Pervasives_Native.None ->
        let result =
          try
            (fun uu___91_6954 ->
               match () with
               | () ->
                   let uu____6957 = FStar_Util.is_path_absolute filename in
                   if uu____6957
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____6964 =
                        let uu____6967 = include_path () in
                        FStar_List.rev uu____6967 in
                      FStar_Util.find_map uu____6964
                        (fun p ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___90_6979 -> FStar_Pervasives_Native.None in
        (match result with
         | FStar_Pervasives_Native.None -> result
         | FStar_Pervasives_Native.Some f ->
             (FStar_Util.smap_add file_map filename f; result))
let (prims : unit -> Prims.string) =
  fun uu____6990 ->
    let uu____6991 = get_prims () in
    match uu____6991 with
    | FStar_Pervasives_Native.None ->
        let filename = "prims.fst" in
        let uu____6995 = find_file filename in
        (match uu____6995 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None ->
             let uu____6999 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename in
             failwith uu____6999)
    | FStar_Pervasives_Native.Some x -> x
let (prims_basename : unit -> Prims.string) =
  fun uu____7005 ->
    let uu____7006 = prims () in FStar_Util.basename uu____7006
let (pervasives : unit -> Prims.string) =
  fun uu____7011 ->
    let filename = "FStar.Pervasives.fst" in
    let uu____7013 = find_file filename in
    match uu____7013 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None ->
        let uu____7017 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____7017
let (pervasives_basename : unit -> Prims.string) =
  fun uu____7022 ->
    let uu____7023 = pervasives () in FStar_Util.basename uu____7023
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____7028 ->
    let filename = "FStar.Pervasives.Native.fst" in
    let uu____7030 = find_file filename in
    match uu____7030 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None ->
        let uu____7034 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename in
        failwith uu____7034
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname ->
    let uu____7040 = get_odir () in
    match uu____7040 with
    | FStar_Pervasives_Native.None -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath ->
    let uu____7049 = get_cache_dir () in
    match uu____7049 with
    | FStar_Pervasives_Native.None -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____7053 = FStar_Util.basename fpath in
        FStar_Util.join_paths x uu____7053
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text -> FStar_String.split [46] text
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list, Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun ns ->
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if FStar_Util.starts_with s "-"
        then
          (let path =
             let uu____7119 =
               FStar_Util.substring_from s (Prims.parse_int "1") in
             path_of_text uu____7119 in
           (path, false))
        else
          (let s1 =
             if FStar_Util.starts_with s "+"
             then FStar_Util.substring_from s (Prims.parse_int "1")
             else s in
           ((path_of_text s1), true)) in
    let uu____7127 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s ->
              FStar_All.pipe_right (FStar_Util.split s " ")
                (FStar_List.map parse_one_setting))) in
    FStar_All.pipe_right uu____7127 FStar_List.rev
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s ->
    let uu____7197 = get___temp_no_proj () in
    FStar_All.pipe_right uu____7197 (FStar_List.contains s)
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____7206 -> lookup_opt "__temp_fast_implicits" as_bool
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____7211 -> get_admit_smt_queries ()
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7218 -> get_admit_except ()
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____7223 -> get_cache_checked_modules ()
let (cache_off : unit -> Prims.bool) = fun uu____7228 -> get_cache_off ()
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee -> match projectee with | OCaml -> true | uu____7234 -> false
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee ->
    match projectee with | FSharp -> true | uu____7240 -> false
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Kremlin -> true | uu____7246 -> false
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Plugin -> true | uu____7252 -> false
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____7259 ->
    let uu____7260 = get_codegen () in
    FStar_Util.map_opt uu____7260
      (fun uu___85_7264 ->
         match uu___85_7264 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____7265 -> failwith "Impossible")
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____7274 ->
    let uu____7275 = get_codegen_lib () in
    FStar_All.pipe_right uu____7275
      (FStar_List.map (fun x -> FStar_Util.split x "."))
let (debug_any : unit -> Prims.bool) =
  fun uu____7292 -> let uu____7293 = get_debug () in uu____7293 <> []
let (debug_module : Prims.string -> Prims.bool) =
  fun modul ->
    let uu____7303 = get_debug () in
    FStar_All.pipe_right uu____7303 (FStar_List.contains modul)
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul ->
    fun level ->
      (let uu____7320 = get_debug () in
       FStar_All.pipe_right uu____7320 (FStar_List.contains modul)) &&
        (debug_level_geq level)
let (defensive : unit -> Prims.bool) =
  fun uu____7329 -> let uu____7330 = get_defensive () in uu____7330 <> "no"
let (defensive_fail : unit -> Prims.bool) =
  fun uu____7335 -> let uu____7336 = get_defensive () in uu____7336 = "fail"
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7343 -> get_dep ()
let (detail_errors : unit -> Prims.bool) =
  fun uu____7348 -> get_detail_errors ()
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____7353 -> get_detail_hint_replay ()
let (doc : unit -> Prims.bool) = fun uu____7358 -> get_doc ()
let (dump_module : Prims.string -> Prims.bool) =
  fun s ->
    let uu____7364 = get_dump_module () in
    FStar_All.pipe_right uu____7364 (FStar_List.contains s)
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____7373 -> get_eager_subtyping ()
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____7378 -> get_expose_interfaces ()
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename ->
    let uu____7384 = FStar_ST.op_Bang light_off_files in
    FStar_List.contains filename uu____7384
let (full_context_dependency : unit -> Prims.bool) = fun uu____7414 -> true
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____7419 -> get_hide_uvar_nums ()
let (hint_info : unit -> Prims.bool) =
  fun uu____7424 -> (get_hint_info ()) || (get_query_stats ())
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7431 -> get_hint_file ()
let (ide : unit -> Prims.bool) = fun uu____7436 -> get_ide ()
let (indent : unit -> Prims.bool) = fun uu____7441 -> get_indent ()
let (initial_fuel : unit -> Prims.int) =
  fun uu____7446 ->
    let uu____7447 = get_initial_fuel () in
    let uu____7448 = get_max_fuel () in Prims.min uu____7447 uu____7448
let (initial_ifuel : unit -> Prims.int) =
  fun uu____7453 ->
    let uu____7454 = get_initial_ifuel () in
    let uu____7455 = get_max_ifuel () in Prims.min uu____7454 uu____7455
let (interactive : unit -> Prims.bool) =
  fun uu____7460 -> (get_in ()) || (get_ide ())
let (lax : unit -> Prims.bool) = fun uu____7465 -> get_lax ()
let (load : unit -> Prims.string Prims.list) = fun uu____7472 -> get_load ()
let (legacy_interactive : unit -> Prims.bool) = fun uu____7477 -> get_in ()
let (log_queries : unit -> Prims.bool) = fun uu____7482 -> get_log_queries ()
let (log_types : unit -> Prims.bool) = fun uu____7487 -> get_log_types ()
let (max_fuel : unit -> Prims.int) = fun uu____7492 -> get_max_fuel ()
let (max_ifuel : unit -> Prims.int) = fun uu____7497 -> get_max_ifuel ()
let (min_fuel : unit -> Prims.int) = fun uu____7502 -> get_min_fuel ()
let (ml_ish : unit -> Prims.bool) = fun uu____7507 -> get_MLish ()
let (set_ml_ish : unit -> unit) =
  fun uu____7512 -> set_option "MLish" (Bool true)
let (n_cores : unit -> Prims.int) = fun uu____7517 -> get_n_cores ()
let (no_default_includes : unit -> Prims.bool) =
  fun uu____7522 -> get_no_default_includes ()
let (no_extract : Prims.string -> Prims.bool) =
  fun s ->
    let s1 = FStar_String.lowercase s in
    let uu____7529 = get_no_extract () in
    FStar_All.pipe_right uu____7529
      (FStar_Util.for_some (fun f -> (FStar_String.lowercase f) = s1))
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____7540 -> get_normalize_pure_terms_for_extraction ()
let (no_location_info : unit -> Prims.bool) =
  fun uu____7545 -> get_no_location_info ()
let (no_plugins : unit -> Prims.bool) = fun uu____7550 -> get_no_plugins ()
let (no_smt : unit -> Prims.bool) = fun uu____7555 -> get_no_smt ()
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7562 -> get_odir ()
let (ugly : unit -> Prims.bool) = fun uu____7567 -> get_ugly ()
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____7572 -> get_print_bound_var_types ()
let (print_effect_args : unit -> Prims.bool) =
  fun uu____7577 -> get_print_effect_args ()
let (print_implicits : unit -> Prims.bool) =
  fun uu____7582 -> get_print_implicits ()
let (print_real_names : unit -> Prims.bool) =
  fun uu____7587 -> (get_prn ()) || (get_print_full_names ())
let (print_universes : unit -> Prims.bool) =
  fun uu____7592 -> get_print_universes ()
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____7597 -> (get_print_z3_statistics ()) || (get_query_stats ())
let (query_stats : unit -> Prims.bool) = fun uu____7602 -> get_query_stats ()
let (record_hints : unit -> Prims.bool) =
  fun uu____7607 -> get_record_hints ()
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7614 -> get_reuse_hint_for ()
let (silent : unit -> Prims.bool) = fun uu____7619 -> get_silent ()
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____7624 -> get_smtencoding_elim_box ()
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____7629 ->
    let uu____7630 = get_smtencoding_nl_arith_repr () in
    uu____7630 = "native"
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____7635 ->
    let uu____7636 = get_smtencoding_nl_arith_repr () in
    uu____7636 = "wrapped"
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____7641 ->
    let uu____7642 = get_smtencoding_nl_arith_repr () in
    uu____7642 = "boxwrap"
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____7647 ->
    let uu____7648 = get_smtencoding_l_arith_repr () in uu____7648 = "native"
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____7653 ->
    let uu____7654 = get_smtencoding_l_arith_repr () in
    uu____7654 = "boxwrap"
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____7659 -> get_tactic_raw_binders ()
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____7664 -> get_tactics_failhard ()
let (tactics_info : unit -> Prims.bool) =
  fun uu____7669 -> get_tactics_info ()
let (tactic_trace : unit -> Prims.bool) =
  fun uu____7674 -> get_tactic_trace ()
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____7679 -> get_tactic_trace_d ()
let (tactics_nbe : unit -> Prims.bool) = fun uu____7684 -> get_tactics_nbe ()
let (tcnorm : unit -> Prims.bool) = fun uu____7689 -> get_tcnorm ()
let (timing : unit -> Prims.bool) = fun uu____7694 -> get_timing ()
let (trace_error : unit -> Prims.bool) = fun uu____7699 -> get_trace_error ()
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____7704 -> get_unthrottle_inductives ()
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____7709 -> get_unsafe_tactic_exec ()
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____7714 -> get_use_eq_at_higher_order ()
let (use_hints : unit -> Prims.bool) = fun uu____7719 -> get_use_hints ()
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____7724 -> get_use_hint_hashes ()
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____7731 -> get_use_native_tactics ()
let (use_tactics : unit -> Prims.bool) = fun uu____7736 -> get_use_tactics ()
let (using_facts_from :
  unit ->
    (Prims.string Prims.list, Prims.bool) FStar_Pervasives_Native.tuple2
      Prims.list)
  =
  fun uu____7749 ->
    let uu____7750 = get_using_facts_from () in
    match uu____7750 with
    | FStar_Pervasives_Native.None -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____7788 ->
    let uu____7789 = get_vcgen_optimize_bind_as_seq () in
    FStar_Option.isSome uu____7789
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____7796 ->
    let uu____7797 = get_vcgen_optimize_bind_as_seq () in
    match uu____7797 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____7800 -> false
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____7807 -> get_warn_default_effects ()
let (z3_exe : unit -> Prims.string) =
  fun uu____7812 ->
    let uu____7813 = get_smt () in
    match uu____7813 with
    | FStar_Pervasives_Native.None -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____7823 -> get_z3cliopt ()
let (z3_refresh : unit -> Prims.bool) = fun uu____7828 -> get_z3refresh ()
let (z3_rlimit : unit -> Prims.int) = fun uu____7833 -> get_z3rlimit ()
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____7838 -> get_z3rlimit_factor ()
let (z3_seed : unit -> Prims.int) = fun uu____7843 -> get_z3seed ()
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____7848 ->
    (get_use_two_phase_tc ()) &&
      (let uu____7850 = lax () in Prims.op_Negation uu____7850)
let (no_positivity : unit -> Prims.bool) =
  fun uu____7855 -> get_no_positivity ()
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____7860 -> get_ml_no_eta_expand_coertions ()
let (warn_error : unit -> Prims.string) = fun uu____7865 -> get_warn_error ()
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____7870 -> get_use_extracted_interfaces ()
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f ->
    let uu____7886 =
      let uu____7887 = trace_error () in Prims.op_Negation uu____7887 in
    if uu____7886
    then
      (push ();
       (try
          (fun uu___93_7892 ->
             match () with | () -> let retv = f () in (pop (); retv)) ()
        with | uu___92_7897 -> (pop (); FStar_Exn.raise uu___92_7897)))
    else (push (); (let retv = f () in pop (); retv))
let (should_extract : Prims.string -> Prims.bool) =
  fun m ->
    let m1 = FStar_String.lowercase m in
    let uu____7909 = get_extract () in
    match uu____7909 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____7920 =
            let uu____7933 = get_no_extract () in
            let uu____7936 = get_extract_namespace () in
            let uu____7939 = get_extract_module () in
            (uu____7933, uu____7936, uu____7939) in
          match uu____7920 with
          | ([], [], []) -> ()
          | uu____7954 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         (let setting = parse_settings extract_setting in
          let m_components = path_of_text m1 in
          let rec matches_path m_components1 path =
            match (m_components1, path) with
            | (uu____8002, []) -> true
            | (m2::ms, p::ps) ->
                (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
            | uu____8021 -> false in
          let uu____8030 =
            FStar_All.pipe_right setting
              (FStar_Util.try_find
                 (fun uu____8064 ->
                    match uu____8064 with
                    | (path, uu____8072) -> matches_path m_components path)) in
          match uu____8030 with
          | FStar_Pervasives_Native.None -> false
          | FStar_Pervasives_Native.Some (uu____8083, flag) -> flag))
    | FStar_Pervasives_Native.None ->
        let should_extract_namespace m2 =
          let uu____8103 = get_extract_namespace () in
          match uu____8103 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1 ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1))) in
        let should_extract_module m2 =
          let uu____8119 = get_extract_module () in
          match uu____8119 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1 -> (FStar_String.lowercase n1) = m2)) in
        (let uu____8131 = no_extract m1 in Prims.op_Negation uu____8131) &&
          (let uu____8133 =
             let uu____8142 = get_extract_namespace () in
             let uu____8145 = get_extract_module () in
             (uu____8142, uu____8145) in
           (match uu____8133 with
            | ([], []) -> true
            | uu____8156 ->
                (should_extract_namespace m1) || (should_extract_module m1)))